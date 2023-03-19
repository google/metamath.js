
axiom df-fcf
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  assert |- fClusf = ( j e. Top , f e. U. ran Fil |-> ( g e. ( U. j ^m U. f ) |-> ( j fClus ( ( U. j FilMap g ) ` f ) ) ) )
end
