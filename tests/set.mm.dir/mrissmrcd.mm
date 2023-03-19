include "wpss.mm"
include "wn.mm"
include "wceq.mm"
include "cfv.mm"
include "mressmrcd.mm"
include "pssne.mm"
include "necomd.mm"
include "necon2bi.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "mrissd.mm"
include "mrieqv2d.mm"
include "mpbid.mm"
include "cvv.mm"
include "ssexd.mm"
include "wa.mm"
include "simpr.mm"
include "psseq1d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "spcdv.mm"
include "mpd.mm"
include "mtod.mm"
include "wss.mm"
include "wo.mm"
include "sspss.mm"
include "sylib.mm"
include "ord.mm"
include "eqcomd.mm"

theorem mrissmrcd
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume mrissmrcd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mrissmrcd.2: |- N = ( mrCls ` A )
  assume mrissmrcd.3: |- I = ( mrInd ` A )
  assume mrissmrcd.4: |- ( ph -> S C_ ( N ` T ) )
  assume mrissmrcd.5: |- ( ph -> T C_ S )
  assume mrissmrcd.6: |- ( ph -> S e. I )


  assert |- ( ph -> S = T )

  proof
    wph
    cT
    cS
    wph
    cT
    cS
    wpss
    #
    wn
    cT
    cS
    wceq
    #
    wph
    @0
    cT
    cN
    cfv
    #
    cS
    cN
    cfv
    #
    wpss
    #
    wph
    @3
    @2
    wceq
    @4
    wn
    wph
    cA
    cS
    cT
    cN
    cX
    mrissmrcd.1
    mrissmrcd.2
    mrissmrcd.4
    mrissmrcd.5
    mressmrcd
    @4
    @3
    @2
    @4
    @2
    @3
    @2
    @3
    pssne
    necomd
    necon2bi
    syl
    wph
    vs
    cv
    #
    cS
    wpss
    #
    @5
    cN
    cfv
    #
    @3
    wpss
    #
    wi
    #
    vs
    wal
    #
    @0
    @4
    wi
    #
    wph
    cS
    cI
    wcel
    @10
    mrissmrcd.6
    wph
    cA
    cS
    cI
    cN
    cX
    vs
    mrissmrcd.1
    mrissmrcd.2
    mrissmrcd.3
    wph
    cA
    cS
    cI
    cX
    mrissmrcd.3
    mrissmrcd.1
    mrissmrcd.6
    mrissd
    mrieqv2d
    mpbid
    wph
    @9
    @11
    vs
    cT
    cvv
    wph
    cT
    cS
    cI
    mrissmrcd.6
    mrissmrcd.5
    ssexd
    wph
    @5
    cT
    wceq
    #
    wa
    #
    @6
    @0
    @8
    @4
    @13
    @5
    cT
    cS
    wph
    @12
    simpr
    #
    psseq1d
    @13
    @7
    @2
    @3
    @13
    @5
    cT
    cN
    @14
    fveq2d
    psseq1d
    imbi12d
    spcdv
    mpd
    mtod
    wph
    @0
    @1
    wph
    cT
    cS
    wss
    @0
    @1
    wo
    mrissmrcd.5
    cT
    cS
    sspss
    sylib
    ord
    mpd
    eqcomd
end
