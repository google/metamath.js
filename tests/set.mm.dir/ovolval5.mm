include "covol.mm"
include "cfv.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cvol.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "clt.mm"
include "cinf.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "wb.mm"
include "coeq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvrabv.mm"
include "ovolval4.mm"
include "ovolval5lem3.mm"
include "eqtrd.mm"

theorem ovolval5
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cM: class M
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let vk: setvar k
  assume ovolval5.a: |- ( ph -> A C_ RR )
  assume ovolval5.m: |- M = { y e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( [,) o. f ) /\ y = ( sum^ ` ( ( vol o. [,) ) o. f ) ) ) }

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint M y
  disjoint ph y
  disjoint A g
  disjoint A x
  disjoint A z
  disjoint f g
  disjoint f x
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M z
  disjoint k x
  assert |- ( ph -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    cA
    covol
    cfv
    cA
    cioo
    vg
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    vx
    cv
    #
    cvol
    cioo
    ccom
    #
    @0
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vg
    cr
    cr
    cxp
    cn
    cmap
    co
    #
    wrex
    #
    vx
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cM
    cxr
    clt
    cinf
    #
    wph
    vy
    cA
    vf
    @13
    ovolval5.a
    @12
    cA
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    vy
    cv
    #
    @6
    @16
    ccom
    #
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    #
    vx
    vy
    cxr
    @5
    @21
    wceq
    #
    @12
    @4
    @21
    @8
    wceq
    #
    wa
    #
    vg
    @11
    wrex
    #
    @26
    @27
    @10
    @29
    vg
    @11
    @27
    @9
    @28
    @4
    @5
    @21
    @8
    eqeq1
    anbi2d
    rexbidv
    @30
    @26
    wb
    @27
    @29
    @25
    vg
    vf
    @11
    @0
    @16
    wceq
    #
    @4
    @20
    @28
    @24
    @31
    @3
    @19
    cA
    @31
    @2
    @18
    @31
    @1
    @17
    @0
    @16
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    #
    @31
    @8
    @23
    @21
    @31
    @7
    @22
    csumge0
    @0
    @16
    @6
    coeq2
    fveq2d
    #
    eqeq2d
    anbi12d
    cbvrexv
    a1i
    bitrd
    cbvrabv
    ovolval4
    @14
    @15
    wceq
    wph
    vy
    vz
    cA
    @13
    vf
    cM
    ovolval5.m
    @12
    @20
    vz
    cv
    #
    @23
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    #
    vx
    vz
    cxr
    @5
    @34
    wceq
    #
    @12
    @20
    @5
    @23
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    #
    @37
    @12
    @41
    wb
    @38
    @10
    @40
    vg
    vf
    @11
    @31
    @4
    @20
    @9
    @39
    @32
    @31
    @8
    @23
    @5
    @33
    eqeq2d
    anbi12d
    cbvrexv
    a1i
    @38
    @40
    @36
    vf
    @11
    @38
    @39
    @35
    @20
    @5
    @34
    @23
    eqeq1
    anbi2d
    rexbidv
    bitrd
    cbvrabv
    ovolval5lem3
    a1i
    eqtrd
end
