include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "chj.mm"
include "cva.mm"
include "wi.mm"
include "wral.mm"
include "chil.mm"
include "wf.mm"
include "cno.mm"
include "c1.mm"
include "ishst.mm"
include "simp3bi.mm"
include "ad2antrr.mm"
include "sseq1.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "sseq2d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "com23.mm"
include "impr.mm"
include "adantll.mm"
include "mpd.mm"

theorem hstel2
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( ( S e. CHStates /\ A e. CH ) /\ ( B e. CH /\ A C_ ( _|_ ` B ) ) ) -> ( ( ( S ` A ) .ih ( S ` B ) ) = 0 /\ ( S ` ( A vH B ) ) = ( ( S ` A ) +h ( S ` B ) ) ) )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    cB
    cch
    wcel
    #
    cA
    cB
    cort
    cfv
    #
    wss
    #
    wa
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cort
    cfv
    #
    wss
    #
    @6
    cS
    cfv
    #
    @7
    cS
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    @6
    @7
    chj
    co
    #
    cS
    cfv
    #
    @10
    @11
    cva
    co
    #
    wceq
    #
    wa
    #
    wi
    #
    vy
    cch
    wral
    vx
    cch
    wral
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    cA
    cB
    chj
    co
    #
    cS
    cfv
    #
    @21
    @22
    cva
    co
    #
    wceq
    #
    wa
    #
    @0
    @20
    @1
    @5
    @0
    cch
    chil
    cS
    wf
    chil
    cS
    cfv
    cno
    cfv
    c1
    wceq
    @20
    vx
    vy
    cS
    ishst
    simp3bi
    ad2antrr
    @1
    @5
    @20
    @29
    wi
    #
    @0
    @1
    @2
    @4
    @30
    @1
    @2
    wa
    @20
    @4
    @29
    @19
    @4
    @29
    wi
    cA
    @8
    wss
    #
    @21
    @11
    csp
    co
    #
    cc0
    wceq
    #
    cA
    @7
    chj
    co
    #
    cS
    cfv
    #
    @21
    @11
    cva
    co
    #
    wceq
    #
    wa
    #
    wi
    vx
    vy
    cA
    cB
    cch
    cch
    @6
    cA
    wceq
    #
    @9
    @31
    @18
    @38
    @6
    cA
    @8
    sseq1
    @39
    @13
    @33
    @17
    @37
    @39
    @12
    @32
    cc0
    @39
    @10
    @21
    @11
    csp
    @6
    cA
    cS
    fveq2
    #
    oveq1d
    eqeq1d
    @39
    @15
    @35
    @16
    @36
    @39
    @14
    @34
    cS
    @6
    cA
    @7
    chj
    oveq1
    fveq2d
    @39
    @10
    @21
    @11
    cva
    @40
    oveq1d
    eqeq12d
    anbi12d
    imbi12d
    @7
    cB
    wceq
    #
    @31
    @4
    @38
    @29
    @41
    @8
    @3
    cA
    @7
    cB
    cort
    fveq2
    sseq2d
    @41
    @33
    @24
    @37
    @28
    @41
    @32
    @23
    cc0
    @41
    @11
    @22
    @21
    csp
    @7
    cB
    cS
    fveq2
    #
    oveq2d
    eqeq1d
    @41
    @35
    @26
    @36
    @27
    @41
    @34
    @25
    cS
    @7
    cB
    cA
    chj
    oveq2
    fveq2d
    @41
    @11
    @22
    @21
    cva
    @42
    oveq2d
    eqeq12d
    anbi12d
    imbi12d
    rspc2v
    com23
    impr
    adantll
    mpd
end
