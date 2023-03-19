include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "eqid.mm"
include "symgfixelsi.mm"
include "fmptd.mm"

theorem symgfixf
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cH: class H
  let cK: class K
  let cN: class N
  let vq: setvar q
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.h: |- H = ( q e. Q |-> ( q |` ( N \ { K } ) ) )

  disjoint K q
  disjoint P q
  disjoint N q
  disjoint Q q
  disjoint S q
  assert |- ( K e. N -> H : Q --> S )

  proof
    cK
    cN
    wcel
    vq
    cQ
    vq
    cv
    #
    cN
    cK
    csn
    cdif
    #
    cres
    cS
    cH
    @1
    cP
    cQ
    cS
    @0
    cK
    cN
    vq
    symgfixf.p
    symgfixf.q
    symgfixf.s
    @1
    eqid
    symgfixelsi
    symgfixf.h
    fmptd
end
