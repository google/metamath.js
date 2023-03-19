include "cn.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wdisj.mm"
include "wa.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wne.mm"
include "nnfoctb.mm"
include "syl2anc.mm"
include "crn.mm"
include "cres.mm"
include "wf1o.mm"
include "cpw.mm"
include "wrex.mm"
include "clt.mm"
include "cvv.mm"
include "wfn.mm"
include "fofn.mm"
include "adantl.mm"
include "wcel.mm"
include "nnex.mm"
include "a1i.mm"
include "wwe.mm"
include "ltwenn.mm"
include "wessf1orn.mm"
include "w3a.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "cmpt.mm"
include "wss.mm"
include "elpwi.mm"
include "3ad2ant2.mm"
include "simpr.mm"
include "forn.mm"
include "adantr.mm"
include "f1oeq3d.mm"
include "mpbid.mm"
include "adantll.mm"
include "3adant2.mm"
include "3ad2ant1.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "notbid.mm"
include "orbi12d.mm"
include "fveq2d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "nnfoctbdjlem.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "exlimdv.mm"

theorem nnfoctbdj
  let wph: wff ph
  let vy: setvar y
  let vf: setvar f
  let vn: setvar n
  let cX: class X
  let vg: setvar g
  let vx: setvar x
  let vm: setvar m
  let vk: setvar k
  assume nnfoctbdj.ctb: |- ( ph -> X ~<_ _om )
  assume nnfoctbdj.n0: |- ( ph -> X =/= (/) )
  assume nnfoctbdj.dj: |- ( ph -> Disj_ y e. X y )

  disjoint X f
  disjoint X n
  disjoint f n
  disjoint X y
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint X g
  disjoint X x
  disjoint f g
  disjoint f x
  disjoint g n
  disjoint g x
  disjoint n x
  disjoint g y
  disjoint x y
  disjoint f m
  disjoint g m
  disjoint m n
  disjoint m x
  disjoint g ph
  disjoint ph x
  disjoint m y
  disjoint k x
  assert |- ( ph -> E. f ( f : NN -onto-> ( X u. { (/) } ) /\ Disj_ n e. NN ( f ` n ) ) )

  proof
    wph
    cn
    cX
    vg
    cv
    #
    wfo
    #
    vg
    wex
    #
    cn
    cX
    c0
    csn
    cun
    vf
    cv
    #
    wfo
    vn
    cn
    vn
    cv
    #
    @3
    cfv
    wdisj
    wa
    vf
    wex
    #
    wph
    cX
    com
    cdom
    wbr
    cX
    c0
    wne
    @2
    nnfoctbdj.ctb
    nnfoctbdj.n0
    cX
    vg
    nnfoctb
    syl2anc
    wph
    @1
    @5
    vg
    wph
    @1
    @5
    wph
    @1
    wa
    #
    vx
    cv
    #
    @0
    crn
    #
    @0
    @7
    cres
    #
    wf1o
    #
    vx
    cn
    cpw
    #
    wrex
    @5
    @6
    vx
    cn
    clt
    @0
    cvv
    @1
    @0
    cn
    wfn
    wph
    cn
    cX
    @0
    fofn
    adantl
    cn
    cvv
    wcel
    @6
    nnex
    a1i
    cn
    clt
    wwe
    @6
    ltwenn
    a1i
    wessf1orn
    @6
    @10
    @5
    vx
    @11
    @6
    @7
    @11
    wcel
    #
    @10
    @5
    @6
    @12
    @10
    w3a
    vy
    @7
    vf
    vn
    vm
    cn
    vm
    cv
    #
    c1
    wceq
    #
    @13
    c1
    cmin
    co
    #
    @7
    wcel
    #
    wn
    #
    wo
    #
    c0
    @15
    @9
    cfv
    #
    cif
    #
    cmpt
    @9
    cX
    @12
    @6
    @7
    cn
    wss
    @10
    @7
    cn
    elpwi
    3ad2ant2
    @6
    @10
    @7
    cX
    @9
    wf1o
    #
    @12
    @1
    @10
    @21
    wph
    @1
    @10
    wa
    #
    @10
    @21
    @1
    @10
    simpr
    @22
    @8
    cX
    @7
    @9
    @1
    @8
    cX
    wceq
    @10
    cn
    cX
    @0
    forn
    adantr
    f1oeq3d
    mpbid
    adantll
    3adant2
    @6
    @12
    vy
    cX
    vy
    cv
    wdisj
    #
    @10
    wph
    @23
    @1
    nnfoctbdj.dj
    adantr
    3ad2ant1
    vm
    vn
    cn
    @20
    @4
    c1
    wceq
    #
    @4
    c1
    cmin
    co
    #
    @7
    wcel
    #
    wn
    #
    wo
    #
    c0
    @25
    @9
    cfv
    #
    cif
    @13
    @4
    wceq
    #
    @18
    @28
    @19
    @29
    c0
    @30
    @14
    @24
    @17
    @27
    @13
    @4
    c1
    eqeq1
    @30
    @16
    @26
    @30
    @15
    @25
    @7
    @13
    @4
    c1
    cmin
    oveq1
    #
    eleq1d
    notbid
    orbi12d
    @30
    @15
    @25
    @9
    @31
    fveq2d
    ifbieq2d
    cbvmptv
    nnfoctbdjlem
    3exp
    rexlimdv
    mpd
    ex
    exlimdv
    mpd
end
