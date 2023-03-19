include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "c7.mm"
include "cpr.mm"
include "cneg.mm"
include "cif.mm"
include "cmul.mm"
include "clgs.mm"
include "wceq.mm"
include "cc.mm"
include "0cn.mm"
include "ax-1cn.mm"
include "neg1cn.mm"
include "keepel.mm"
include "mul02i.mm"
include "iftrue.mm"
include "adantl.mm"
include "oveq1d.mm"
include "wi.mm"
include "2z.mm"
include "dvdsmultr1.mm"
include "mp3an1.mm"
include "imp.mm"
include "iftrued.mm"
include "3eqtr4a.mm"
include "mul01i.mm"
include "oveq2d.mm"
include "dvdsmultr2.mm"
include "wn.mm"
include "mulid2i.mm"
include "wb.mm"
include "lgsdir2lem4.mm"
include "adantlr.mm"
include "ifbid.mm"
include "mulid1i.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "eleq1d.mm"
include "ancom1s.mm"
include "bitrd.mm"
include "neg1mulneg1e1.mm"
include "iffalse.mm"
include "oveqan12d.mm"
include "c3.mm"
include "c5.mm"
include "cun.mm"
include "wo.mm"
include "lgsdir2lem3.mm"
include "ad2ant2r.mm"
include "elun.mm"
include "sylib.mm"
include "orcanai.mm"
include "ad2ant2l.mm"
include "anim12dan.mm"
include "lgsdir2lem5.mm"
include "syldan.mm"
include "pm2.61ddan.mm"
include "ioran.mm"
include "cprime.mm"
include "2prm.mm"
include "euclemma.mm"
include "notbid.mm"
include "biimpar.mm"
include "sylan2br.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "lgs2.mm"
include "zmulcl.mm"
include "3eqtr4rd.mm"

theorem lgsdir2
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A x. B ) /L 2 ) = ( ( A /L 2 ) x. ( B /L 2 ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    c2
    cA
    cdvds
    wbr
    #
    cc0
    cA
    c8
    cmo
    co
    #
    c1
    c7
    cpr
    #
    wcel
    #
    c1
    c1
    cneg
    #
    cif
    #
    cif
    #
    c2
    cB
    cdvds
    wbr
    #
    cc0
    cB
    c8
    cmo
    co
    #
    @5
    wcel
    #
    c1
    @7
    cif
    #
    cif
    #
    cmul
    co
    #
    c2
    cA
    cB
    cmul
    co
    #
    cdvds
    wbr
    #
    cc0
    @16
    c8
    cmo
    co
    #
    @5
    wcel
    #
    c1
    @7
    cif
    #
    cif
    #
    cA
    c2
    clgs
    co
    #
    cB
    c2
    clgs
    co
    #
    cmul
    co
    @16
    c2
    clgs
    co
    #
    @2
    @3
    @10
    @15
    @21
    wceq
    @2
    @3
    wa
    #
    cc0
    @14
    cmul
    co
    cc0
    @15
    @21
    @14
    @10
    cc0
    @13
    cc
    0cn
    @12
    c1
    @7
    cc
    ax-1cn
    neg1cn
    keepel
    #
    keepel
    mul02i
    @25
    @9
    cc0
    @14
    cmul
    @3
    @9
    cc0
    wceq
    @2
    @3
    cc0
    @8
    iftrue
    adantl
    oveq1d
    @25
    @17
    cc0
    @20
    @2
    @3
    @17
    c2
    cz
    wcel
    #
    @0
    @1
    @3
    @17
    wi
    2z
    c2
    cA
    cB
    dvdsmultr1
    mp3an1
    imp
    iftrued
    3eqtr4a
    @2
    @10
    wa
    #
    @9
    cc0
    cmul
    co
    cc0
    @15
    @21
    @9
    @3
    cc0
    @8
    cc
    0cn
    @6
    c1
    @7
    cc
    ax-1cn
    neg1cn
    keepel
    #
    keepel
    mul01i
    @28
    @14
    cc0
    @9
    cmul
    @10
    @14
    cc0
    wceq
    @2
    @10
    cc0
    @13
    iftrue
    adantl
    oveq2d
    @28
    @17
    cc0
    @20
    @2
    @10
    @17
    @27
    @0
    @1
    @10
    @17
    wi
    2z
    c2
    cA
    cB
    dvdsmultr2
    mp3an1
    imp
    iftrued
    3eqtr4a
    @2
    @3
    wn
    #
    @10
    wn
    #
    wa
    #
    wa
    #
    @8
    @13
    cmul
    co
    #
    @20
    @15
    @21
    @33
    @6
    @12
    @34
    @20
    wceq
    @33
    @6
    wa
    #
    c1
    @13
    cmul
    co
    @13
    @34
    @20
    @13
    @26
    mulid2i
    @35
    @8
    c1
    @13
    cmul
    @6
    @8
    c1
    wceq
    @33
    @6
    c1
    @7
    iftrue
    adantl
    oveq1d
    @35
    @19
    @12
    c1
    @7
    @2
    @6
    @19
    @12
    wb
    @32
    cA
    cB
    lgsdir2lem4
    adantlr
    ifbid
    3eqtr4a
    @33
    @12
    wa
    #
    @8
    c1
    cmul
    co
    @8
    @34
    @20
    @8
    @29
    mulid1i
    @36
    @13
    c1
    @8
    cmul
    @12
    @13
    c1
    wceq
    @33
    @12
    c1
    @7
    iftrue
    adantl
    oveq2d
    @36
    @19
    @6
    c1
    @7
    @36
    @19
    cB
    cA
    cmul
    co
    #
    c8
    cmo
    co
    #
    @5
    wcel
    #
    @6
    @36
    @18
    @38
    @5
    @36
    @16
    @37
    c8
    cmo
    @2
    @16
    @37
    wceq
    #
    @32
    @12
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @40
    @1
    cA
    zcn
    cB
    zcn
    cA
    cB
    mulcom
    syl2an
    ad2antrr
    oveq1d
    eleq1d
    @2
    @12
    @39
    @6
    wb
    #
    @32
    @1
    @0
    @12
    @41
    cB
    cA
    lgsdir2lem4
    ancom1s
    adantlr
    bitrd
    ifbid
    3eqtr4a
    @33
    @6
    wn
    #
    @12
    wn
    #
    wa
    #
    wa
    #
    @7
    @7
    cmul
    co
    #
    c1
    @34
    @20
    neg1mulneg1e1
    @44
    @34
    @46
    wceq
    @33
    @42
    @43
    @8
    @7
    @13
    @7
    cmul
    @6
    c1
    @7
    iffalse
    @12
    c1
    @7
    iffalse
    oveqan12d
    adantl
    @45
    @19
    c1
    @7
    @33
    @44
    @4
    c3
    c5
    cpr
    #
    wcel
    #
    @11
    @47
    wcel
    #
    wa
    #
    @19
    @33
    @42
    @48
    @43
    @49
    @33
    @6
    @48
    @33
    @4
    @5
    @47
    cun
    #
    wcel
    #
    @6
    @48
    wo
    @0
    @30
    @52
    @1
    @31
    cA
    lgsdir2lem3
    ad2ant2r
    @4
    @5
    @47
    elun
    sylib
    orcanai
    @33
    @12
    @49
    @33
    @11
    @51
    wcel
    #
    @12
    @49
    wo
    @1
    @31
    @53
    @0
    @30
    cB
    lgsdir2lem3
    ad2ant2l
    @11
    @5
    @47
    elun
    sylib
    orcanai
    anim12dan
    @2
    @50
    @19
    @32
    cA
    cB
    lgsdir2lem5
    adantlr
    syldan
    iftrued
    3eqtr4a
    pm2.61ddan
    @32
    @15
    @34
    wceq
    @2
    @30
    @31
    @9
    @8
    @14
    @13
    cmul
    @3
    cc0
    @8
    iffalse
    @10
    cc0
    @13
    iffalse
    oveqan12d
    adantl
    @33
    @17
    wn
    #
    @21
    @20
    wceq
    @32
    @2
    @3
    @10
    wo
    #
    wn
    #
    @54
    @3
    @10
    ioran
    @2
    @54
    @56
    @2
    @17
    @55
    c2
    cprime
    wcel
    @0
    @1
    @17
    @55
    wb
    2prm
    c2
    cA
    cB
    euclemma
    mp3an1
    notbid
    biimpar
    sylan2br
    @17
    cc0
    @20
    iffalse
    syl
    3eqtr4d
    pm2.61ddan
    @0
    @1
    @22
    @9
    @23
    @14
    cmul
    cA
    lgs2
    cB
    lgs2
    oveqan12d
    @2
    @16
    cz
    wcel
    @24
    @21
    wceq
    cA
    cB
    zmulcl
    @16
    lgs2
    syl
    3eqtr4rd
end
