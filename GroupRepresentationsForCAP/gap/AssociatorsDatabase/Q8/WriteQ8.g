LoadPackage( "GroupRepresentationsForCAP" );
G := QuaternionGroup( 8 );
ComputeAssociator( G, false, true, false );
WriteAssociatorComputationToFiles( "Q8" );



