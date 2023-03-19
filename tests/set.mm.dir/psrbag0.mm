include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wa.mm"
include "0nn0.mm"
include "fconst6.mm"
include "c0.mm"
include "cin.mm"
include "wceq.mm"
include "c0ex.mm"
include "fconst.mm"
include "incom.mm"
include "wn.mm"
include "0nnn.mm"
include "disjsn.mm"
include "mpbir.mm"
include "eqtri.mm"
include "fimacnvdisj.mm"
include "mp2an.mm"
include "0fin.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "psrbag.mm"
include "mpbiri.mm"

theorem psrbag0
  let cD: class D
  let vf: setvar f
  let cI: class I
  let cV: class V
  let vx: setvar x
  let cK: class K
  assume psrbag0.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint I f
  disjoint I x
  disjoint f x
  disjoint K f
  disjoint K x
  assert |- ( I e. V -> ( I X. { 0 } ) e. D )

  proof
    cI
    cV
    wcel
    cI
    cc0
    csn
    #
    cxp
    #
    cD
    wcel
    cI
    cn0
    @1
    wf
    #
    @1
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    wa
    @2
    @4
    cI
    cc0
    cn0
    0nn0
    fconst6
    @3
    c0
    cfn
    cI
    @0
    @1
    wf
    @0
    cn
    cin
    #
    c0
    wceq
    @3
    c0
    wceq
    cI
    cc0
    c0ex
    fconst
    @5
    cn
    @0
    cin
    #
    c0
    @0
    cn
    incom
    @6
    c0
    wceq
    cc0
    cn
    wcel
    wn
    0nnn
    cn
    cc0
    disjsn
    mpbir
    eqtri
    cI
    @0
    cn
    @1
    fimacnvdisj
    mp2an
    0fin
    eqeltri
    pm3.2i
    cD
    vf
    @1
    cI
    cV
    psrbag0.d
    psrbag
    mpbiri
end
