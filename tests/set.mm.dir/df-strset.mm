
axiom df-strset
  let cA: class A
  let cB: class B
  let cS: class S
  assert |- [s B / A ]s S = ( ( S |` ( _V \ { ( A ` ndx ) } ) ) u. { <. ( A ` ndx ) , B >. } )
end
