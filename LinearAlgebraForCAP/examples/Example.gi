#! @Chapter Examples and Tests

#! @Section Basic Commands

LoadPackage( "LinearAlgebraForCAP" );;

#! @Example
Q := HomalgFieldOfRationals();;
a := VectorSpaceObject( 3, Q );
#! <A vector space object over Q of dimension 3>
HasIsProjective( a ) and IsProjective( a );
#! true
vec := MatrixCategory( Q );;
ap := 3/vec;;
IsEqualForObjects( a, ap );
#! true
b := VectorSpaceObject( 4, Q );
#! <A vector space object over Q of dimension 4>
homalg_matrix := HomalgMatrix( [ [ 1, 0, 0, 0 ],
                                  [ 0, 1, 0, -1 ],
                                  [ -1, 0, 2, 1 ] ], 3, 4, Q );
#! <A 3 x 4 matrix over an internal ring>
alpha := VectorSpaceMorphism( a, homalg_matrix, b );
#! <A morphism in Category of matrices over Q>
Display( alpha );
#! [ [   1,   0,   0,   0 ],
#!   [   0,   1,   0,  -1 ],
#!   [  -1,   0,   2,   1 ] ]
#!
#! A morphism in Category of matrices over Q
alphap := homalg_matrix/vec;;
IsCongruentForMorphisms( alpha, alphap );
#! true
homalg_matrix := HomalgMatrix( [ [ 1, 1, 0, 0 ],
                                  [ 0, 1, 0, -1 ],
                                  [ -1, 0, 2, 1 ] ], 3, 4, Q );
#! <A 3 x 4 matrix over an internal ring>
beta := VectorSpaceMorphism( a, homalg_matrix, b );
#! <A morphism in Category of matrices over Q>
CokernelObject( alpha );
#! <A vector space object over Q of dimension 1>
c := CokernelProjection( alpha );;
#! #@if ValueOption( "no_precompiled_code" ) <> true
Display( c );
#! [ [     0 ],
#!   [     1 ],
#!   [  -1/2 ],
#!   [     1 ] ]
#!
#! A split epimorphism in Category of matrices over Q
#! #@fi
gamma := UniversalMorphismIntoDirectSum( [ c, c ] );;
Display( gamma );
#! [ [     0,     0 ],
#!   [     1,     1 ],
#!   [  -1/2,  -1/2 ],
#!   [     1,     1 ] ]
#!
#! A morphism in Category of matrices over Q
colift := CokernelColift( alpha, gamma );;
IsEqualForMorphisms( PreCompose( c, colift ), gamma );
#! true
FiberProduct( alpha, beta );
#! <A vector space object over Q of dimension 2>
F := FiberProduct( alpha, beta );
#! <A vector space object over Q of dimension 2>
p1 := ProjectionInFactorOfFiberProduct( [ alpha, beta ], 1 );
#! <A morphism in Category of matrices over Q>
Display( PreCompose( p1, alpha ) );
#! [ [   0,   1,   0,  -1 ],
#!   [  -1,   0,   2,   1 ] ]
#!
#! A morphism in Category of matrices over Q
Pushout( alpha, beta );
#! <A vector space object over Q of dimension 5>
i1 := InjectionOfCofactorOfPushout( [ alpha, beta ], 1 );
#! <A morphism in Category of matrices over Q>
i2 := InjectionOfCofactorOfPushout( [ alpha, beta ], 2 );
#! <A morphism in Category of matrices over Q>
u := UniversalMorphismFromDirectSum( [ b, b ], [ i1, i2 ] );
#! <A morphism in Category of matrices over Q>
Display( u );
#! [ [     0,     1,     1,     0,     0 ],
#!   [     1,     0,     1,     0,    -1 ],
#!   [  -1/2,     0,   1/2,     1,   1/2 ],
#!   [     1,     0,     0,     0,     0 ],
#!   [     0,     1,     0,     0,     0 ],
#!   [     0,     0,     1,     0,     0 ],
#!   [     0,     0,     0,     1,     0 ],
#!   [     0,     0,     0,     0,     1 ] ]
#!
#! A morphism in Category of matrices over Q
KernelObjectFunctorial( u, IdentityMorphism( Source( u ) ), u ) = IdentityMorphism( VectorSpaceObject( 3, Q ) );
#! true
IsZero( CokernelObjectFunctorial( u, IdentityMorphism( Range( u ) ), u ) );
#! true
DirectProductFunctorial( [ u, u ] ) = DirectSumFunctorial( [ u, u ] );
#! true
CoproductFunctorial( [ u, u ] ) = DirectSumFunctorial( [ u, u ] );
#! true
IsOne( FiberProductFunctorial( [ u, u ], [ IdentityMorphism( Source( u ) ), IdentityMorphism( Source( u ) ) ], [ u, u ] ) );
#! true
IsOne( PushoutFunctorial( [ u, u ], [ IdentityMorphism( Range( u ) ), IdentityMorphism( Range( u ) ) ], [ u, u ] ) );
#! true
IsCongruentForMorphisms( (1/2) * alpha, alpha * (1/2) );
#! true
Dimension( HomomorphismStructureOnObjects( a, b ) ) = Dimension( a ) * Dimension( b );
#! true
IsCongruentForMorphisms(
    PreCompose( [ u, DualOnMorphisms( i1 ), DualOnMorphisms( alpha ) ] ),
    InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( Source( u ), Source( alpha ),
         PreCompose(
             InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( DualOnMorphisms( i1 ) ),
             HomomorphismStructureOnMorphisms( u, DualOnMorphisms( alpha ) )
         )
    )
);
#! true
alpha_op := Opposite( alpha );
#! <A morphism in Opposite( Category of matrices over Q )>
basis := BasisOfExternalHom( Source( alpha_op ), Range( alpha_op ) );;
coeffs := CoefficientsOfMorphism( alpha_op );
#! [ 1, 0, 0, 0, 0, 1, 0, -1, -1, 0, 2, 1 ]
IsEqualForMorphisms( alpha_op, coeffs * basis );
#! true
vec := CapCategory( alpha );;
t := TensorUnit( vec );;
z := ZeroObject( vec );;
IsCongruentForMorphisms(
    ZeroObjectFunctorial( vec ),
    InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( z, z, ZeroMorphism( t, z ) )
);
#! true
IsCongruentForMorphisms(
    ZeroObjectFunctorial( vec ),
    InterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism(
        z, z,
        InterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructure( ZeroObjectFunctorial( vec ) )
    )
);
#! true
right_side := PreCompose( [ i1, DualOnMorphisms( u ), u ] );;
x := SolveLinearSystemInAbCategory( [ [ i1 ] ], [ [ u ] ], [ right_side ] )[1];;
IsCongruentForMorphisms( PreCompose( [ i1, x, u ] ), right_side );
#! true
id_t := IdentityMorphism( t );;
1*(11)*7 + 2*(12)*8 + 3*(13)*9;
#! 620
4*(11)*3 + 5*(12)*4 + 6*(13)*1;
#! 450
left_coeffs :=  [ [ 1 * id_t, 2 * id_t, 3 * id_t ], [ 4 * id_t, 5 * id_t, 6 * id_t ] ];;
right_coeffs := [ [ 7 * id_t, 8 * id_t, 9 * id_t ], [ 3 * id_t, 4 * id_t, 1 * id_t ] ];;
gammas := [ 620 * id_t, 450 * id_t ];;
MereExistenceOfSolutionOfLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );
#! true
MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );
#! false
x := SolveLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );;
1*x[1]*7 + 2*x[2]*8 + 3*x[3]*9 = gammas[1] * id_t;
#! true
4*x[1]*3 + 5*x[2]*4 + 6*x[3]*1 = gammas[2] * id_t;
#! true
MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory( vec, left_coeffs, right_coeffs );
#! false
basis := BasisForSolutionsOfHomogeneousLinearSystemInLinearCategory( vec, left_coeffs, right_coeffs );;
Length( basis );
#! 1
Display( basis[1][1] );
#! [ [  111/13 ] ]
#!
#! A morphism in Category of matrices over Q
Display( basis[1][2] );
#! [ [  -141/26 ] ]
#!
#! A morphism in Category of matrices over Q
Display( basis[1][3] );
#! [ [  1 ] ]
#!
#! A morphism in Category of matrices over Q
2*(11)*5 + 3*(12)*7 + 9*(13)*2;
#! 596
Add( left_coeffs,  [ 2 * id_t, 3 * id_t, 9 * id_t ] );
Add( right_coeffs, [ 5 * id_t, 7 * id_t, 2 * id_t ] );
Add( gammas, 596 * id_t );
MereExistenceOfSolutionOfLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );
#! true
MereExistenceOfUniqueSolutionOfLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );
#! true
x := SolveLinearSystemInAbCategory( vec, left_coeffs, right_coeffs, gammas );;
1*x[1]*7 + 2*x[2]*8 + 3*x[3]*9 = gammas[1] * id_t;
#! true
4*x[1]*3 + 5*x[2]*4 + 6*x[3]*1 = gammas[2] * id_t;
#! true
2*x[1]*5 + 3*x[2]*7 + 9*x[3]*2 = gammas[3] * id_t;
#! true
MereExistenceOfUniqueSolutionOfHomogeneousLinearSystemInAbCategory( vec, left_coeffs, right_coeffs );
#! true
basis := BasisForSolutionsOfHomogeneousLinearSystemInLinearCategory( vec, left_coeffs, right_coeffs );
#! [ ]
a_otimes_b := TensorProductOnObjects( a, b );
#! <A vector space object over Q of dimension 12>
hom_ab := InternalHomOnObjects( a, b );
#! <A vector space object over Q of dimension 12>
cohom_ab := InternalCoHomOnObjects( a, b );
#! <A vector space object over Q of dimension 12>
hom_ab = cohom_ab;
#! true
1_ab := VectorSpaceMorphism(
          a_otimes_b,
          HomalgIdentityMatrix( Dimension( a_otimes_b ), Q ),
          a_otimes_b
          );
#! <A morphism in Category of matrices over Q>
1_hom_ab := VectorSpaceMorphism(
              hom_ab,
              HomalgIdentityMatrix( Dimension( hom_ab ), Q ),
              hom_ab
            );
#! <A morphism in Category of matrices over Q>
1_cohom_ab := VectorSpaceMorphism(
                cohom_ab,
                HomalgIdentityMatrix( Dimension( cohom_ab ), Q ),
                cohom_ab
              );
#! <A morphism in Category of matrices over Q>
ev_ab := EvaluationMorphism( a, b );
#! <A morphism in Category of matrices over Q>
coev_ab := CoevaluationMorphism( a, b );
#! <A morphism in Category of matrices over Q>
cocl_ev_ab := CoclosedEvaluationMorphism( a, b );
#! <A morphism in Category of matrices over Q>
cocl_ev_ba := CoclosedEvaluationMorphism( b, a );
#! <A morphism in Category of matrices over Q>
cocl_coev_ab := CoclosedCoevaluationMorphism( a, b );
#! <A morphism in Category of matrices over Q>
UnderlyingMatrix( ev_ab ) = TransposedMatrix( UnderlyingMatrix( cocl_ev_ba ) );
#! true
UnderlyingMatrix( coev_ab ) = TransposedMatrix( UnderlyingMatrix( cocl_coev_ab ) );
#! true
tensor_hom_adj_1_hom_ab := InternalHomToTensorProductAdjunctionMap( a, b, 1_hom_ab );
#! <A morphism in Category of matrices over Q>
cohom_tensor_adj_1_cohom_ab := InternalCoHomToTensorProductAdjunctionMap( a, b, 1_cohom_ab );
#! <A morphism in Category of matrices over Q>
tensor_hom_adj_1_ab := TensorProductToInternalHomAdjunctionMap( a, b, 1_ab );
#! <A morphism in Category of matrices over Q>
cohom_tensor_adj_1_ab := TensorProductToInternalCoHomAdjunctionMap( a, b, 1_ab );
#! <A morphism in Category of matrices over Q>
ev_ab = tensor_hom_adj_1_hom_ab;
#! true
cocl_ev_ab = cohom_tensor_adj_1_cohom_ab;
#! true
coev_ab = tensor_hom_adj_1_ab;
#! true
cocl_coev_ab = cohom_tensor_adj_1_ab;
#! true
c := VectorSpaceObject(2,Q);
#! <A vector space object over Q of dimension 2>
d := VectorSpaceObject(1,Q);
#! <A vector space object over Q of dimension 1>
pre_compose := MonoidalPreComposeMorphism( a, b, c );
#! <A morphism in Category of matrices over Q>
post_compose := MonoidalPostComposeMorphism( a, b, c );
#! <A morphism in Category of matrices over Q>
pre_cocompose := MonoidalPreCoComposeMorphism( c, b, a );
#! <A morphism in Category of matrices over Q>
post_cocompose := MonoidalPostCoComposeMorphism( c, b, a );
#! <A morphism in Category of matrices over Q>
UnderlyingMatrix( pre_compose ) = TransposedMatrix( UnderlyingMatrix( pre_cocompose ) );
#! true
UnderlyingMatrix( post_compose ) = TransposedMatrix( UnderlyingMatrix( post_cocompose ) );
#! true
tp_hom_comp := TensorProductInternalHomCompatibilityMorphism( [ a, b, c, d ] );
#! <A morphism in Category of matrices over Q>
cohom_tp_comp := InternalCoHomTensorProductCompatibilityMorphism( [ b, d, a, c ] );
#! <A morphism in Category of matrices over Q>
UnderlyingMatrix( tp_hom_comp ) = TransposedMatrix( UnderlyingMatrix( cohom_tp_comp ) );
#! true
lambda := LambdaIntroduction( alpha );
#! <A morphism in Category of matrices over Q>
lambda_elim := LambdaElimination( a, b, lambda );
#! <A morphism in Category of matrices over Q>
alpha = lambda_elim;
#! true
alpha_op := VectorSpaceMorphism( b, TransposedMatrix( UnderlyingMatrix( alpha ) ), a );
#! <A morphism in Category of matrices over Q>
colambda := CoLambdaIntroduction( alpha_op );
#! <A morphism in Category of matrices over Q>
colambda_elim := CoLambdaElimination( b, a, colambda );
#! <A morphism in Category of matrices over Q>
alpha_op = colambda_elim;
#! true
UnderlyingMatrix( lambda ) = TransposedMatrix( UnderlyingMatrix( colambda ) );
#! true
delta := PreCompose( colambda, lambda);
#! <A morphism in Category of matrices over Q>
Display( TraceMap( delta ) );
#! [ [  9 ] ]
#!
#! A morphism in Category of matrices over Q
Display( CoTraceMap( delta ) );
#! [ [  9 ] ]
#!
#! A morphism in Category of matrices over Q
TraceMap( delta ) = CoTraceMap( delta );
#! true
RankMorphism( a ) = CoRankMorphism( a );
#! true
#! @EndExample
