include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "ccnv.mm"
include "wceq.mm"
include "wf1o.mm"
include "cv.mm"
include "cdif.mm"
include "cfv.mm"
include "cmpt.mm"
include "dssmapfvd.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "pwexg.mm"
include "syl.mm"
include "mptexg.mm"
include "ralrimivw.mm"
include "nfcv.mm"
include "fnmptf.mm"
include "fneq1.mm"
include "biimprd.mm"
include "sylc.mm"
include "dssmapnvod.mm"
include "nvof1o.mm"
include "syl2anc.mm"

theorem dssmapf1od
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vf: setvar f
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
  assume dssmapfvd.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapfvd.d: |- D = ( O ` B )
  assume dssmapfvd.b: |- ( ph -> B e. V )

  disjoint B b
  disjoint B f
  disjoint B s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint b ph
  disjoint f ph
  disjoint ph s
  assert |- ( ph -> D : ( ~P B ^m ~P B ) -1-1-onto-> ( ~P B ^m ~P B ) )

  proof
    wph
    cD
    cB
    cpw
    #
    @0
    cmap
    co
    #
    wfn
    #
    cD
    ccnv
    cD
    wceq
    @1
    @1
    cD
    wf1o
    wph
    cD
    vf
    @1
    vs
    @0
    cB
    cB
    vs
    cv
    cdif
    vf
    cv
    cfv
    cdif
    #
    cmpt
    #
    cmpt
    #
    wceq
    #
    @5
    @1
    wfn
    #
    @2
    wph
    cB
    cD
    vf
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapfvd
    wph
    @4
    cvv
    wcel
    #
    vf
    @1
    wral
    @7
    wph
    @8
    vf
    @1
    wph
    @0
    cvv
    wcel
    #
    @8
    wph
    cB
    cV
    wcel
    @9
    dssmapfvd.b
    cB
    cV
    pwexg
    syl
    vs
    @0
    @3
    cvv
    mptexg
    syl
    ralrimivw
    vf
    @1
    @4
    cvv
    vf
    @1
    nfcv
    fnmptf
    syl
    @6
    @2
    @7
    @1
    cD
    @5
    fneq1
    biimprd
    sylc
    wph
    cB
    cD
    vf
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapnvod
    @1
    cD
    nvof1o
    syl2anc
end
