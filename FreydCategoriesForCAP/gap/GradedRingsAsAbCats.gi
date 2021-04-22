# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Implementations
#

####################################
##
## Constructors
##
####################################

##
InstallMethod( GradedRingAsCategory,
               [ IsHomalgGradedRing ],
               
  function( ring )
    local finalize_option, category;
    
    finalize_option := CAP_INTERNAL_RETURN_OPTION_OR_DEFAULT( "FinalizeCategory", true );
    
    category := CreateCapCategory( Concatenation( "Graded ring as category( ", String( ring )," )" ) );
    
    SetFilterObj( category, IsGradedRingAsCategory );
    
    SetUnderlyingGradedRing( category, ring );
    
    SetIsAbCategory( category, true );
    
    AddObjectRepresentation( category, IsGradedRingAsCategoryObject );
    
    AddMorphismRepresentation( category, IsGradedRingAsCategoryMorphism and HasUnderlyingRingElement );
    
    INSTALL_FUNCTIONS_FOR_GRADED_RING_AS_CATEGORY( category );
    
    DeactivateCachingOfCategory( category );
    DisableSanityChecks( category );
    CapCategorySwitchLogicOff( category );
    
    if finalize_option then
        
        Finalize( category );
        
    fi;
    
    return category;
    
end );

##
InstallMethod( GradedRingAsCategoryObjectOp,
               [ IsGradedRingAsCategory, IsHomalgModuleElement ],
               
  function( category, object )
    
    return ObjectifyObjectForCAPWithAttributes( rec( ),
                                                category,
                                                UnderlyingDegree, object
    );
    
end );

##
InstallMethod( GradedRingAsCategoryMorphism,
               [ IsGradedRingAsCategoryObject, IsHomalgGradedRingElement, IsGradedRingAsCategoryObject ],
               
  function( source, element, range )
    local category;
    
    category := CapCategory( source );
    
    ## this is a "compiled" version of ObjectifyMorphismForCAPWithAttributes
    return ObjectifyWithAttributes( rec(), category!.morphism_type,
                                    Source, source,
                                    Range, range,
                                    UnderlyingRingElement, element,
                                    CapCategory, category
    );
    
end );

####################################
##
## View
##
####################################

##
InstallMethod( Display, [ IsGradedRingAsCategoryMorphism ], ViewObj );

##
InstallMethod( ViewObj,
               [ IsGradedRingAsCategoryMorphism ],
               
    function( alpha )
        
        ViewObj( Source( alpha ) );
        Print( "-[" );
        Print( ViewString( UnderlyingRingElement( alpha ) ) );
        Print( "]->" );
        ViewObj( Range( alpha ) );
        
end );

##
InstallMethod( Display, [ IsGradedRingAsCategoryObject ], ViewObj );

##
InstallMethod( ViewObj,
               [ IsGradedRingAsCategoryObject ],
               
    function( obj )
        
      Print( Concatenation( "<", ViewString( UnderlyingDegree( obj ) ), ">" ) );
        
end );

####################################
##
## Basic operations
##
####################################

InstallGlobalFunction( INSTALL_FUNCTIONS_FOR_GRADED_RING_AS_CATEGORY,
  
  function( category )
    local ring, base_ring, equality_func;
   
    ring := UnderlyingGradedRing( category );
    
    base_ring := UnderlyingNonGradedRing( CoefficientsRing( ring ) );
    
    if HasIsCommutative( base_ring ) and IsCommutative( base_ring ) then
      
      SetIsLinearCategoryOverCommutativeRing( category, true );
      
      SetCommutativeRingOfLinearCategory( category, base_ring );
      
    fi;
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( category,
      {e, alpha} -> GradedRingAsCategoryMorphism( Source( alpha ), ( e / ring ) * UnderlyingRingElement( alpha ), Range( alpha ) )
    );
    
    ##
    AddIsEqualForObjects( category, {obj1, obj2} -> UnderlyingDegree( obj1 ) = UnderlyingDegree( obj2 ) );
    
    equality_func := {alpha, beta} -> UnderlyingRingElement( alpha ) = UnderlyingRingElement( beta );
    
    ##
    AddIsEqualForMorphisms( category, equality_func );
    
    ##
    AddIsCongruentForMorphisms( category, equality_func );
    
    ##
    AddIsWellDefinedForObjects( category, x -> IsIdenticalObj( SuperObject( UnderlyingDegree( x ) ), DegreeGroup( ring ) ) );
    
    ##
    AddIsWellDefinedForMorphisms( category,
      function( alpha )
        
        return Degree( UnderlyingRingElement( alpha ) ) = UnderlyingDegree( Range( alpha ) ) - UnderlyingDegree( Source( alpha ) );
        
    end );
    
    ##
    AddPreCompose( category,
      function( alpha, beta )
        
        return GradedRingAsCategoryMorphism(
                  Source( alpha ),
                  UnderlyingRingElement( alpha ) * UnderlyingRingElement( beta ),
                  Range( beta )
        );
        
    end );
    
    ##
    AddIdentityMorphism( category,
      function( a )
        
        return GradedRingAsCategoryMorphism( a, One( ring ), a );
        
    end );
    
    ##
    AddIsOne( category,
      function( alpha )
        
        return IsOne( UnderlyingRingElement( alpha ) );
        
    end );
    
    ##
    AddZeroMorphism( category,
      function( a, b )
        
        return GradedRingAsCategoryMorphism( a, Zero( ring ), b );
        
    end );
    
    ##
    AddIsZeroForMorphisms( category,
      function( alpha )
        
        return IsZero( UnderlyingRingElement( alpha ) );
        
    end );
    
    ##
    AddAdditionForMorphisms( category,
      function( alpha, beta )
        
        return GradedRingAsCategoryMorphism(
                    Source( alpha ),
                    UnderlyingRingElement( alpha ) + UnderlyingRingElement( beta ),
                    Range( alpha )
        );
        
    end );
    
    ##
    AddAdditiveInverseForMorphisms( category,
      function( alpha )
        
        return GradedRingAsCategoryMorphism(
                    Source( alpha ),
                    - UnderlyingRingElement( alpha ),
                    Range( alpha )
        );
        
    end );
    
    ## Homomorphism structure
    
    SetRangeCategoryOfHomomorphismStructure( category, MatrixCategory( base_ring ) );
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( category,
      {} -> VectorSpaceObject( 1, base_ring )
    );
    
    ##
    AddHomomorphismStructureOnObjects( category,
      function( a, b )
        local monomials, H_ab;
        
        monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( b ) - UnderlyingDegree( a ) );
        
        H_ab := Size( monomials ) / RangeCategoryOfHomomorphismStructure( category );
         
        return H_ab;
        
    end );
     
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( category,
      function( s, alpha, beta, r )
        local s_monomials, H_bc, r_monomials, H_ad;
        
        s_monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( Source( beta ) ) - UnderlyingDegree( Range( alpha ) ) );
        
        H_bc := HomalgMatrix( UnderlyingRingElement( alpha ) * s_monomials * UnderlyingRingElement( beta ), ring );
        
        r_monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( Range( beta ) ) - UnderlyingDegree( Source( alpha ) ) );
        
        H_ad := HomalgMatrix( r_monomials, ring );
        
        if NrCols( H_bc ) = 0 or NrCols( H_ad ) = 0 then
          return ZeroMorphism( s, r );
        else
          return VectorSpaceMorphism( s, RightDivide( H_bc, H_ad ) * base_ring, r );
        fi;
        
    end );
    
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( category,
      function( alpha )
        local one, H_ab, monomials, coeffs;
        
        one := DistinguishedObjectOfHomomorphismStructure( category );
        
        H_ab := HomomorphismStructureOnObjects( Source( alpha ), Range( alpha ) );
        
        monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( Range( alpha ) ) - UnderlyingDegree( Source( alpha ) ) );
        
        if Dimension( H_ab ) = 0 then
          return ZeroMorphism( one, H_ab );
        fi;
        
        coeffs := CoefficientsWithGivenMonomials(
                        UnderlyingNonGradedRingElement( UnderlyingRingElement( alpha ) ),
                        HomalgMatrix( monomials, ring ) * UnderlyingNonGradedRing( ring )
                    ) * base_ring;
        
        return VectorSpaceMorphism( one, coeffs, H_ab );
        
    end );
    
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( category,
      function( a, b, alpha )
        local monomials;
        
        monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( b ) - UnderlyingDegree( a ) );
        
        if IsEmpty( monomials ) then
          return ZeroMorphism( a, b );
        else
          alpha := EntriesOfHomalgMatrix( UnderlyingMatrix( alpha ) * ring ) * monomials;
          return GradedRingAsCategoryMorphism( a, alpha, b );
        fi;
        
    end );
    
    ##
    AddBasisOfExternalHom( category,
      function( a, b )
        local monomials;
        
        monomials := MonomialsWithGivenDegree( ring, UnderlyingDegree( b ) - UnderlyingDegree( a ) );
        
        return List( monomials, m -> GradedRingAsCategoryMorphism( a, m, b ) );
        
    end );
    
    ##
    InstallMethod( CoefficientsOfMorphism,
              [ IsGradedRingAsCategoryMorphism and MorphismFilter( category ) ],
      alpha -> EntriesOfHomalgMatrix( UnderlyingMatrix( InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( alpha ) ) )
    );
    
    ##
    AddCoefficientsOfMorphismWithGivenBasisOfExternalHom( category,
      { alpha, basis } -> CoefficientsOfMorphism( alpha )
    );
    
    AddRandomObjectByInteger( category,
      function( cat, n )
        return GradedRingAsCategoryObject( cat, Sum( List( [ 1 .. n ], i -> Degree( Random( Concatenation( [ One( ring ) ], Indeterminates( ring ) ) ) ) ) ) );
    end );
    
    AddRandomMorphismWithFixedSourceAndRangeByInteger( category,
      function( a, b, n )
        local B_ab;
        
        B_ab := BasisOfExternalHom( a, b );
        
        if IsEmpty( B_ab ) then
          return ZeroMorphism( a, b );
        else
          return Sum( List( [ 1 .. n ], i -> Random( B_ab ) ) );
        fi;
        
    end );

    AddRandomMorphismByInteger( category,
      function( cat, n )
        local a, b;
        
        a := RandomObject( cat, Int( n/2 ) );
        
        b := RandomObject( cat, Random( [ Int( n/2 ) .. n ] ) );
        
        return RandomMorphismWithFixedSourceAndRangeByInteger( a, b, n );
        
    end );
    
end );


####################################
##
## Additive Closure & Functors
##
####################################

##
InstallMethod( AdditiveClosure,
          [ IsGradedRingAsCategory ],
          
  function( category )
    local o, finalize, ring, matrix_element_as_morphism, list_list_as_matrix;
    
    o := ValueOption( "GradedRingsAsAbCats_AdditiveClosure" );
    
    if o = false then
      TryNextMethod( );
    fi;
    
    finalize := ValueOption( "FinalizeCategory" );
    
    ring := UnderlyingGradedRing( category );
    
    matrix_element_as_morphism :=
      { morphism, i, j } -> GradedRingAsCategoryMorphism(
                                    Source( morphism )[ i ],
                                    MorphismMatrix( morphism )[ i, j ],
                                    Range( morphism )[ j ]
                            );
    
    list_list_as_matrix :=
      { listlist, m, n } -> HomalgMatrix(
                              List( listlist, list -> List( list, UnderlyingRingElement ) ), m, n, ring
                            );
   
    category := AdditiveClosure( category : GradedRingsAsAbCats_AdditiveClosure := false,
                                      matrix_element_as_morphism := matrix_element_as_morphism,
                                      list_list_as_matrix := list_list_as_matrix,
                                      FinalizeCategory := finalize );
    
    ## This is a hot fix, until the original behavior matrix_element_as_morphism is updated
    ## ( This is needed because matrix element might not be enough to determine the morphism
    ## We need three arguments: morphism, row_index, col_index to extract the source & range )
    
    ##
    InstallMethod( \[\,\],
                   [ IsAdditiveClosureMorphism and MorphismFilter( category ), IsInt, IsInt ],
                   
      function( morphism, i, j )
        local matrix_element_as_morphism;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        if not ( i in [ 1 .. NrRows( morphism ) ]
            and j in [ 1 .. NrCols( morphism ) ] ) then
            
            Error( "bad index!\n" );
            
        fi;
        
        matrix_element_as_morphism := CapCategory( morphism )!.matrix_element_as_morphism;
        
        return matrix_element_as_morphism( morphism, i, j );
        
    end );
    
    DeactivateCachingOfCategory( category );
    DisableSanityChecks( category );
    CapCategorySwitchLogicOff( category );
    
    return category;
    
end );


##
InstallMethod( InclusionFunctorInCategoryOfGradedRows,
          [ IsGradedRingAsCategory ],
          
  function( category )
    local ring, graded_rows, name, F;
    
    ring := UnderlyingGradedRing( category );
    
    graded_rows := CategoryOfGradedRows( ring );
    
    name := "Inclusion functor";
    
    F := CapFunctor( name, category, graded_rows );
    
    AddObjectFunction( F,
      obj -> GradedRow( [ [ UnderlyingDegree( obj ), 1 ] ], ring )
    );
    
    AddMorphismFunction( F,
      { s, alpha, r } -> GradedRowOrColumnMorphism(
                                s,
                                HomalgMatrix( [[UnderlyingRingElement( alpha )]], 1, 1, ring ),
                                r
                            )
    );
    
    return F;
    
end );

##
InstallMethod( IsomorphismFromAdditiveClosureOfGradedRingAsCategory,
          [ IsCategoryOfGradedRows ],
          
  function( graded_rows )
    local ring, ring_cat, I;
    
    ring := UnderlyingGradedRing( graded_rows );
    
    ring_cat := GradedRingAsCategory( ring );
    
    I := InclusionFunctorInCategoryOfGradedRows( ring_cat );
    
    I := ExtendFunctorToAdditiveClosureOfSource( I );
    
    I!.Name := "Isomorphism functor";
    
    return I;
    
end);

##
InstallMethod( IsomorphismOntoAdditiveClosureOfGradedRingAsCategory,
          [ IsCategoryOfGradedRows ],
          
  function( graded_rows )
    local ring, ring_cat, ring_cat_plus, name, F;
    
    ring := UnderlyingGradedRing( graded_rows );
    
    ring_cat := GradedRingAsCategory( ring );
    
    ring_cat_plus := AdditiveClosure( ring_cat );
    
    name := "Isomorphism functor";
    
    F := CapFunctor( name, graded_rows, ring_cat_plus );
    
    AddObjectFunction( F,
      grow -> List( UnzipDegreeList( grow ), degree -> degree / ring_cat ) / ring_cat_plus
    );
    
    AddMorphismFunction( F,
      {s, alpha, r } -> AdditiveClosureMorphism( s, UnderlyingHomalgMatrix( alpha ), r )
    );
    
    return F;
    
end );


####################################
##
## Convenience
##
####################################

InstallMethod( \=,
               [ IsGradedRingAsCategoryMorphism, IsGradedRingAsCategoryMorphism ],
               IsCongruentForMorphisms );

InstallMethod( \/,
               [ IsObject, IsGradedRingAsCategory ],
    { degree, category } -> GradedRingAsCategoryObject( category, degree )
);

####################################
##
## Down
##
####################################

##
InstallMethod( Down,
               [ IsGradedRingAsCategoryObject ],
               UnderlyingDegree );

##
InstallMethod( DownOnlyMorphismData,
               [ IsGradedRingAsCategoryMorphism ],
               UnderlyingRingElement );
