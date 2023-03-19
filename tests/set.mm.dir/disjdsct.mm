include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wceq.mm"
include "csb.mm"
include "wne.mm"
include "wo.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wdisj.mm"
include "disjorsf.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "w3a.mm"
include "simpr3.mm"
include "wsb.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsni.mm"
include "syl.mm"
include "sbimi.mm"
include "sban.mm"
include "sbf.mm"
include "clelsb3f.mm"
include "anbi12i.mm"
include "bitri.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "sbcne12.mm"
include "csb0.mm"
include "neeq2i.mm"
include "3bitri.mm"
include "3imtr3i.mm"
include "3ad2antr1.mm"
include "disj3.mm"
include "biimpi.mm"
include "neeq1d.mm"
include "biimpa.mm"
include "difn0.mm"
include "syl2anc.mm"
include "3anassrs.mm"
include "ex.mm"
include "orim2d.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "nfmpt1.mm"
include "eqid.mm"
include "funcnv4mpt.mm"
include "mpbird.mm"

theorem disjdsct
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume disjdsct.0: |- F/ x ph
  assume disjdsct.1: |- F/_ x A
  assume disjdsct.2: |- ( ( ph /\ x e. A ) -> B e. ( V \ { (/) } ) )
  assume disjdsct.3: |- ( ph -> Disj_ x e. A B )

  disjoint V x
  disjoint i j
  disjoint i x
  disjoint j x
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> Fun `' ( x e. A |-> B ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    ccnv
    wfun
    vi
    cv
    #
    vj
    cv
    #
    wceq
    #
    vx
    @1
    cB
    csb
    #
    vx
    @2
    cB
    csb
    #
    wne
    #
    wo
    #
    vj
    cA
    wral
    #
    vi
    cA
    wral
    wph
    @8
    vi
    cA
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @7
    vj
    cA
    @10
    @2
    cA
    wcel
    #
    wa
    #
    @3
    @4
    @5
    cin
    c0
    wceq
    #
    wo
    #
    @7
    @10
    @14
    vj
    cA
    wph
    @14
    vj
    cA
    wral
    #
    vi
    cA
    wph
    vx
    cA
    cB
    wdisj
    @15
    vi
    cA
    wral
    disjdsct.3
    vx
    cA
    cB
    vi
    vj
    disjdsct.1
    disjorsf
    sylib
    r19.21bi
    r19.21bi
    @12
    @13
    @6
    @3
    @12
    @13
    @6
    wph
    @9
    @11
    @13
    @6
    wph
    @9
    @11
    @13
    w3a
    wa
    @13
    @4
    c0
    wne
    #
    @6
    wph
    @9
    @11
    @13
    simpr3
    wph
    @11
    @9
    @16
    @13
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vx
    vi
    wsb
    #
    cB
    c0
    wne
    #
    vx
    vi
    wsb
    #
    @10
    @16
    @18
    @20
    vx
    vi
    @18
    cB
    cV
    c0
    csn
    cdif
    #
    wcel
    @20
    disjdsct.2
    cB
    cV
    c0
    eldifsni
    syl
    sbimi
    @19
    wph
    vx
    vi
    wsb
    #
    @17
    vx
    vi
    wsb
    #
    wa
    @10
    wph
    @17
    vx
    vi
    sban
    @23
    wph
    @24
    @9
    wph
    vx
    vi
    disjdsct.0
    sbf
    vi
    vx
    cA
    disjdsct.1
    clelsb3f
    anbi12i
    bitri
    @21
    @20
    vx
    @1
    wsbc
    @4
    vx
    @1
    c0
    csb
    #
    wne
    @16
    @20
    vx
    vi
    sbsbc
    vx
    @1
    cB
    c0
    sbcne12
    @25
    c0
    @4
    vx
    @1
    csb0
    neeq2i
    3bitri
    3imtr3i
    3ad2antr1
    @13
    @16
    wa
    @4
    @5
    cdif
    #
    c0
    wne
    #
    @6
    @13
    @16
    @27
    @13
    @4
    @26
    c0
    @13
    @4
    @26
    wceq
    @4
    @5
    disj3
    biimpi
    neeq1d
    biimpa
    @4
    @5
    difn0
    syl
    syl2anc
    3anassrs
    ex
    orim2d
    mpd
    ralrimiva
    ralrimiva
    wph
    vx
    cA
    cB
    vi
    vj
    @0
    @22
    disjdsct.0
    disjdsct.1
    vx
    cA
    cB
    nfmpt1
    @0
    eqid
    disjdsct.2
    funcnv4mpt
    mpbird
end
