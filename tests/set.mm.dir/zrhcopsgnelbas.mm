include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "zrhcofipsgn.mm"
include "3adant1.mm"
include "zrhpsgnelbas.mm"
include "eqeltrd.mm"

theorem zrhcopsgnelbas
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cN: class N
  let cY: class Y
  assume zrhpsgnelbas.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhpsgnelbas.s: |- S = ( pmSgn ` N )
  assume zrhpsgnelbas.y: |- Y = ( ZRHom ` R )


  assert |- ( ( R e. Ring /\ N e. Fin /\ Q e. P ) -> ( ( Y o. S ) ` Q ) e. ( Base ` R ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    cQ
    cP
    wcel
    #
    w3a
    cQ
    cY
    cS
    ccom
    cfv
    #
    cQ
    cS
    cfv
    cY
    cfv
    #
    cR
    cbs
    cfv
    @1
    @2
    @3
    @4
    wceq
    @0
    cP
    cQ
    cR
    cS
    cN
    cY
    zrhpsgnelbas.p
    zrhpsgnelbas.y
    zrhpsgnelbas.s
    zrhcofipsgn
    3adant1
    cP
    cQ
    cR
    cS
    cN
    cY
    zrhpsgnelbas.p
    zrhpsgnelbas.s
    zrhpsgnelbas.y
    zrhpsgnelbas
    eqeltrd
end
