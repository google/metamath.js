
axiom df-fullfun
  let cF: class F
  assert |- FullFun F = ( Funpart F u. ( ( _V \ dom Funpart F ) X. { (/) } ) )
end
