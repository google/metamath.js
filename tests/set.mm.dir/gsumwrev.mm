include "cword.mm"
include "wcel.mm"
include "cmnd.mm"
include "cgsu.mm"
include "co.mm"
include "creverse.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "cs1.mm"
include "cconcat.mm"
include "oveq2.mm"
include "fveq2.mm"
include "rev0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0g.mm"
include "eqid.mm"
include "oppgid.mm"
include "gsum0.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "wa.mm"
include "cplusg.mm"
include "oppgmnd.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "s1cld.mm"
include "oppgbas.mm"
include "gsumccat.mm"
include "syl3anc.mm"
include "gsumws1.mm"
include "ad2antll.mm"
include "oppgplus.mm"
include "eqtrd.mm"
include "revccat.mm"
include "syl2anc.mm"
include "revs1.mm"
include "oveq1i.mm"
include "simpl.mm"
include "revcl.mm"
include "ad2antrl.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "wrdind.mm"
include "impcom.mm"

theorem gsumwrev
  let cB: class B
  let cM: class M
  let cO: class O
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume gsumwrev.b: |- B = ( Base ` M )
  assume gsumwrev.o: |- O = ( oppG ` M )


  assert |- ( ( M e. Mnd /\ W e. Word B ) -> ( O gsum W ) = ( M gsum ( reverse ` W ) ) )

  proof
    cW
    cB
    cword
    #
    wcel
    cM
    cmnd
    wcel
    #
    cO
    cW
    cgsu
    co
    #
    cM
    cW
    creverse
    cfv
    #
    cgsu
    co
    #
    wceq
    #
    @1
    cO
    vx
    cv
    #
    cgsu
    co
    #
    cM
    @6
    creverse
    cfv
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @1
    cO
    c0
    cgsu
    co
    #
    cM
    c0
    cgsu
    co
    #
    wceq
    #
    wi
    @1
    cO
    vy
    cv
    #
    cgsu
    co
    #
    cM
    @14
    creverse
    cfv
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @1
    cO
    @14
    vz
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cgsu
    co
    #
    cM
    @21
    creverse
    cfv
    #
    cgsu
    co
    #
    wceq
    #
    wi
    @1
    @5
    wi
    vx
    vy
    vz
    cW
    cB
    @6
    c0
    wceq
    #
    @10
    @13
    @1
    @26
    @7
    @11
    @9
    @12
    @6
    c0
    cO
    cgsu
    oveq2
    @26
    @8
    c0
    cM
    cgsu
    @26
    @8
    c0
    creverse
    cfv
    c0
    @6
    c0
    creverse
    fveq2
    rev0
    syl6eq
    oveq2d
    eqeq12d
    imbi2d
    @6
    @14
    wceq
    #
    @10
    @18
    @1
    @27
    @7
    @15
    @9
    @17
    @6
    @14
    cO
    cgsu
    oveq2
    @27
    @8
    @16
    cM
    cgsu
    @6
    @14
    creverse
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @6
    @21
    wceq
    #
    @10
    @25
    @1
    @28
    @7
    @22
    @9
    @24
    @6
    @21
    cO
    cgsu
    oveq2
    @28
    @8
    @23
    cM
    cgsu
    @6
    @21
    creverse
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @6
    cW
    wceq
    #
    @10
    @5
    @1
    @29
    @7
    @2
    @9
    @4
    @6
    cW
    cO
    cgsu
    oveq2
    @29
    @8
    @3
    cM
    cgsu
    @6
    cW
    creverse
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @13
    @1
    @11
    cM
    c0g
    cfv
    #
    @12
    cO
    @30
    cM
    cO
    @30
    gsumwrev.o
    @30
    eqid
    #
    oppgid
    gsum0
    cM
    @30
    @31
    gsum0
    eqtr4i
    a1i
    @14
    @0
    wcel
    #
    @19
    cB
    wcel
    #
    wa
    #
    @1
    @18
    @25
    @1
    @34
    @18
    @25
    wi
    @18
    @25
    @1
    @34
    wa
    #
    @19
    @15
    cM
    cplusg
    cfv
    #
    co
    #
    @19
    @17
    @36
    co
    #
    wceq
    @15
    @17
    @19
    @36
    oveq2
    @35
    @22
    @37
    @24
    @38
    @35
    @22
    @15
    cO
    @20
    cgsu
    co
    #
    cO
    cplusg
    cfv
    #
    co
    #
    @37
    @35
    cO
    cmnd
    wcel
    #
    @32
    @20
    @0
    wcel
    #
    @22
    @41
    wceq
    @1
    @42
    @34
    cM
    cO
    gsumwrev.o
    oppgmnd
    adantr
    @1
    @32
    @33
    simprl
    #
    @35
    @19
    cB
    @1
    @32
    @33
    simprr
    s1cld
    #
    cB
    @40
    cO
    @14
    @20
    cB
    cM
    cO
    gsumwrev.o
    gsumwrev.b
    oppgbas
    #
    @40
    eqid
    #
    gsumccat
    syl3anc
    @35
    @41
    @15
    @19
    @40
    co
    @37
    @35
    @39
    @19
    @15
    @40
    @33
    @39
    @19
    wceq
    @1
    @32
    cB
    @19
    cO
    @46
    gsumws1
    ad2antll
    oveq2d
    @36
    @40
    cM
    cO
    @15
    @19
    @36
    eqid
    #
    gsumwrev.o
    @47
    oppgplus
    syl6eq
    eqtrd
    @35
    @24
    cM
    @20
    @16
    cconcat
    co
    #
    cgsu
    co
    #
    cM
    @20
    cgsu
    co
    #
    @17
    @36
    co
    #
    @38
    @35
    @23
    @49
    cM
    cgsu
    @35
    @23
    @20
    creverse
    cfv
    #
    @16
    cconcat
    co
    #
    @49
    @35
    @32
    @43
    @23
    @54
    wceq
    @44
    @45
    cB
    @14
    @20
    revccat
    syl2anc
    @53
    @20
    @16
    cconcat
    @19
    revs1
    oveq1i
    syl6eq
    oveq2d
    @35
    @1
    @43
    @16
    @0
    wcel
    #
    @50
    @52
    wceq
    @1
    @34
    simpl
    @45
    @32
    @55
    @1
    @33
    cB
    @14
    revcl
    ad2antrl
    cB
    @36
    cM
    @20
    @16
    gsumwrev.b
    @48
    gsumccat
    syl3anc
    @35
    @51
    @19
    @17
    @36
    @33
    @51
    @19
    wceq
    @1
    @32
    cB
    @19
    cM
    gsumwrev.b
    gsumws1
    ad2antll
    oveq1d
    3eqtrd
    eqeq12d
    syl5ibr
    expcom
    a2d
    wrdind
    impcom
end
