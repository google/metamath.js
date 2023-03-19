include "wcel.mm"
include "cres.mm"
include "csn.mm"
include "cdif.mm"
include "csymg.mm"
include "cfv.mm"
include "cbs.mm"
include "wf1o.mm"
include "wb.mm"
include "eleq2i.mm"
include "a1i.mm"
include "cvv.mm"
include "resexg.mm"
include "eqid.mm"
include "elsymgbas2.mm"
include "syl.mm"
include "eqidd.mm"
include "wceq.mm"
include "eqcomd.mm"
include "f1oeq123d.mm"
include "3bitrd.mm"

theorem symgfixels
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let vq: setvar q
  assume symgfixf.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume symgfixf.q: |- Q = { q e. P | ( q ` K ) = K }
  assume symgfixf.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgfixf.d: |- D = ( N \ { K } )

  disjoint K q
  disjoint P q
  assert |- ( F e. V -> ( ( F |` D ) e. S <-> ( F |` D ) : D -1-1-onto-> D ) )

  proof
    cF
    cV
    wcel
    #
    cF
    cD
    cres
    #
    cS
    wcel
    #
    @1
    cN
    cK
    csn
    cdif
    #
    csymg
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @3
    @1
    wf1o
    #
    cD
    cD
    @1
    wf1o
    @2
    @6
    wb
    @0
    cS
    @5
    @1
    symgfixf.s
    eleq2i
    a1i
    @0
    @1
    cvv
    wcel
    @6
    @7
    wb
    cF
    cD
    cV
    resexg
    @3
    @5
    @1
    @4
    cvv
    @4
    eqid
    @5
    eqid
    elsymgbas2
    syl
    @0
    @3
    cD
    @3
    cD
    @1
    @1
    @0
    @1
    eqidd
    @0
    cD
    @3
    cD
    @3
    wceq
    @0
    symgfixf.d
    a1i
    eqcomd
    #
    @8
    f1oeq123d
    3bitrd
end
