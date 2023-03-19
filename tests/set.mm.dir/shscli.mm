include "cph.mm"
include "co.mm"
include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "c0v.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "wral.mm"
include "csm.mm"
include "cc.mm"
include "shsss.mm"
include "mp2an.mm"
include "wceq.mm"
include "wrex.mm"
include "sh0.mm"
include "ax-mp.mm"
include "ax-hv0cl.mm"
include "hvaddid2i.mm"
include "eqcomi.mm"
include "rspceov.mm"
include "mp3an.mm"
include "shseli.mm"
include "mpbir.mm"
include "pm3.2i.mm"
include "wi.mm"
include "shaddcl.mm"
include "mp3an1.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "oveq12.mm"
include "sheli.mm"
include "anim12i.mm"
include "hvadd4.mm"
include "syl2an.mm"
include "an4s.mm"
include "eqtr4d.mm"
include "syl3anc.mm"
include "ancoms.mm"
include "exp43.mm"
include "rexlimivv.mm"
include "com3l.mm"
include "imp.mm"
include "syl2anb.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "shmulcl.mm"
include "adantrr.mm"
include "adantrl.mm"
include "oveq2.mm"
include "adantl.mm"
include "ad2antll.mm"
include "id.mm"
include "ax-hvdistr1.mm"
include "syl3an.mm"
include "3expb.mm"
include "adantrrr.mm"
include "eqtrd.mm"
include "exp42.mm"
include "impcom.mm"
include "sylan2b.mm"
include "rgen2.mm"
include "issh2.mm"
include "mpbir2an.mm"

theorem shscli
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cD: class D
  assume shscl.1: |- A e. SH
  assume shscl.2: |- B e. SH


  assert |- ( A +H B ) e. SH

  proof
    cA
    cB
    cph
    co
    #
    csh
    wcel
    @0
    chil
    wss
    #
    c0v
    @0
    wcel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cva
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    @0
    wral
    #
    @3
    @4
    csm
    co
    #
    @0
    wcel
    #
    vy
    @0
    wral
    vx
    cc
    wral
    #
    wa
    @1
    @2
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    @1
    shscl.1
    shscl.2
    cA
    cB
    shsss
    mp2an
    @2
    c0v
    @5
    wceq
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    c0v
    cA
    wcel
    #
    c0v
    cB
    wcel
    #
    c0v
    c0v
    c0v
    cva
    co
    #
    wceq
    @13
    @11
    @14
    shscl.1
    cA
    sh0
    ax-mp
    @12
    @15
    shscl.2
    cB
    sh0
    ax-mp
    @16
    c0v
    c0v
    ax-hv0cl
    hvaddid2i
    eqcomi
    vx
    vy
    cA
    cB
    c0v
    c0v
    c0v
    cva
    rspceov
    mp3an
    vx
    vy
    cA
    cB
    c0v
    shscl.1
    shscl.2
    shseli
    mpbir
    pm3.2i
    @7
    @10
    @6
    vx
    vy
    @0
    @3
    @0
    wcel
    #
    @4
    @0
    wcel
    #
    wa
    @5
    vf
    cv
    vg
    cv
    cva
    co
    #
    wceq
    vg
    cB
    wrex
    vf
    cA
    wrex
    #
    @6
    @17
    @3
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vw
    cB
    wrex
    vz
    cA
    wrex
    #
    @4
    vv
    cv
    #
    vu
    cv
    #
    cva
    co
    #
    wceq
    #
    vu
    cB
    wrex
    vv
    cA
    wrex
    #
    @20
    @18
    vz
    vw
    cA
    cB
    @3
    shscl.1
    shscl.2
    shseli
    vv
    vu
    cA
    cB
    @4
    shscl.1
    shscl.2
    shseli
    #
    @25
    @30
    @20
    @24
    @30
    @20
    wi
    vz
    vw
    cA
    cB
    @30
    @21
    cA
    wcel
    #
    @22
    cB
    wcel
    #
    wa
    #
    @24
    @20
    @29
    @34
    @24
    @20
    wi
    wi
    vv
    vu
    cA
    cB
    @26
    cA
    wcel
    #
    @27
    cB
    wcel
    #
    wa
    #
    @29
    @34
    @24
    @20
    @34
    @24
    wa
    #
    @37
    @29
    wa
    #
    @20
    @38
    @39
    wa
    #
    @21
    @26
    cva
    co
    #
    cA
    wcel
    #
    @22
    @27
    cva
    co
    #
    cB
    wcel
    #
    @5
    @41
    @43
    cva
    co
    #
    wceq
    @20
    @34
    @37
    @42
    @24
    @29
    @32
    @35
    @42
    @33
    @36
    @11
    @32
    @35
    @42
    shscl.1
    @21
    @26
    cA
    shaddcl
    mp3an1
    ad2ant2r
    ad2ant2r
    @34
    @37
    @44
    @24
    @29
    @33
    @36
    @44
    @32
    @35
    @12
    @33
    @36
    @44
    shscl.2
    @22
    @27
    cB
    shaddcl
    mp3an1
    ad2ant2l
    ad2ant2r
    @40
    @5
    @23
    @28
    cva
    co
    #
    @45
    @24
    @29
    @5
    @46
    wceq
    @34
    @37
    @3
    @23
    @4
    @28
    cva
    oveq12
    ad2ant2l
    @34
    @37
    @45
    @46
    wceq
    #
    @24
    @29
    @32
    @35
    @33
    @36
    @47
    @32
    @35
    wa
    @21
    chil
    wcel
    #
    @26
    chil
    wcel
    #
    wa
    @22
    chil
    wcel
    #
    @27
    chil
    wcel
    #
    wa
    @47
    @33
    @36
    wa
    @32
    @48
    @35
    @49
    @21
    cA
    shscl.1
    sheli
    @26
    cA
    shscl.1
    sheli
    #
    anim12i
    @33
    @50
    @36
    @51
    @22
    cB
    shscl.2
    sheli
    @27
    cB
    shscl.2
    sheli
    #
    anim12i
    @21
    @26
    @22
    @27
    hvadd4
    syl2an
    an4s
    ad2ant2r
    eqtr4d
    vf
    vg
    cA
    cB
    @41
    @43
    @5
    cva
    rspceov
    syl3anc
    ancoms
    exp43
    rexlimivv
    com3l
    rexlimivv
    imp
    syl2anb
    vf
    vg
    cA
    cB
    @5
    shscl.1
    shscl.2
    shseli
    sylibr
    rgen2a
    @9
    vx
    vy
    cc
    @0
    @3
    cc
    wcel
    #
    @18
    wa
    @8
    @19
    wceq
    vg
    cB
    wrex
    vf
    cA
    wrex
    #
    @9
    @18
    @54
    @30
    @55
    @31
    @30
    @54
    @55
    @29
    @54
    @55
    wi
    #
    vv
    vu
    cA
    cB
    @35
    @36
    @29
    @56
    wi
    @35
    @36
    @29
    @54
    @55
    @54
    @35
    @36
    @29
    wa
    #
    wa
    #
    @55
    @54
    @58
    wa
    #
    @3
    @26
    csm
    co
    #
    cA
    wcel
    #
    @3
    @27
    csm
    co
    #
    cB
    wcel
    #
    @8
    @60
    @62
    cva
    co
    #
    wceq
    @55
    @54
    @35
    @61
    @57
    @11
    @54
    @35
    @61
    shscl.1
    @3
    @26
    cA
    shmulcl
    mp3an1
    adantrr
    @54
    @57
    @63
    @35
    @54
    @36
    @63
    @29
    @12
    @54
    @36
    @63
    shscl.2
    @3
    @27
    cB
    shmulcl
    mp3an1
    adantrr
    adantrl
    @59
    @8
    @3
    @28
    csm
    co
    #
    @64
    @57
    @8
    @65
    wceq
    #
    @54
    @35
    @29
    @66
    @36
    @4
    @28
    @3
    csm
    oveq2
    adantl
    ad2antll
    @54
    @35
    @36
    @65
    @64
    wceq
    #
    @29
    @54
    @35
    @36
    @67
    @54
    @54
    @35
    @49
    @36
    @51
    @67
    @54
    id
    @52
    @53
    @3
    @26
    @27
    ax-hvdistr1
    syl3an
    3expb
    adantrrr
    eqtrd
    vf
    vg
    cA
    cB
    @60
    @62
    @8
    cva
    rspceov
    syl3anc
    ancoms
    exp42
    imp
    rexlimivv
    impcom
    sylan2b
    vf
    vg
    cA
    cB
    @8
    shscl.1
    shscl.2
    shseli
    sylibr
    rgen2
    pm3.2i
    vx
    vy
    @0
    issh2
    mpbir2an
end
