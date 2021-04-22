# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Declarations
#
#! @Chapter Rings as categories

####################################
##
#! @Section GAP Categories
##
####################################

##
DeclareCategory( "IsGradedRingAsCategoryObject",
                 IsCapCategoryObject );

DeclareCategory( "IsGradedRingAsCategoryMorphism",
                 IsCapCategoryMorphism );

DeclareCategory( "IsGradedRingAsCategory",
                 IsCapCategory );

DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_GRADED_RING_AS_CATEGORY" );

####################################
##
#! @Section Constructors
##
####################################

DeclareAttribute( "GradedRingAsCategory",
                  IsRing );

DeclareAttribute( "GradedRingAsCategoryObject",
                  IsGradedRingAsCategory );

DeclareOperation( "GradedRingAsCategoryMorphism",
                  [ IsObject, IsGradedRingAsCategory ] );

KeyDependentOperation( "GradedRingAsCategoryObject", IsGradedRingAsCategory, IsHomalgModuleElement, ReturnTrue );

DeclareOperation( "GradedRingAsCategoryMorphism",
          [ IsGradedRingAsCategoryObject, IsHomalgGradedRingElement, IsGradedRingAsCategoryObject ] );


####################################
##
#! @Section Attributes
##
####################################

DeclareAttribute( "UnderlyingDegree",
                  IsGradedRingAsCategoryObject );

DeclareAttribute( "UnderlyingRingElement",
                  IsGradedRingAsCategoryMorphism );

DeclareAttribute( "UnderlyingGradedRing",
                  IsGradedRingAsCategory );

####################################
##
#! @Section Operations
##
####################################

##
DeclareAttribute( "InclusionFunctorInCategoryOfGradedRows", IsGradedRingAsCategory );

##
DeclareAttribute( "IsomorphismOntoAdditiveClosureOfGradedRingAsCategory", IsCategoryOfGradedRows );
DeclareAttribute( "IsomorphismFromAdditiveClosureOfGradedRingAsCategory", IsCategoryOfGradedRows );

##
DeclareOperation( "\/",
                  [ IsObject, IsGradedRingAsCategory ] );
