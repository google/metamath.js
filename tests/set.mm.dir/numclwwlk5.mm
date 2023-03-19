include "crusgr.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cprime.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wa.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "chash.mm"
include "cmo.mm"
include "wceq.mm"
include "wi.mm"
include "c2.mm"
include "cn0.mm"
include "simpl1.mm"
include "simpr1.mm"
include "cfusgr.mm"
include "c0.mm"
include "wne.mm"
include "finrusgrfusgr.mm"
include "3adant2.mm"
include "adantl.mm"
include "ne0i.mm"
include "adantr.mm"
include "frusgrnn0.mm"
include "syl3anc.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "3jca.mm"
include "simpr3.mm"
include "numclwwlk5lem.mm"
include "sylc.mm"
include "a1i.mm"
include "eleq1.mm"
include "breq1.mm"
include "3anbi23d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "cmul.mm"
include "cexp.mm"
include "caddc.mm"
include "c3.mm"
include "cuz.mm"
include "3simpa.mm"
include "simprl3.mm"
include "simprr1.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "oddprmge3.mm"
include "sylbir.mm"
include "3ad2ant2.mm"
include "numclwwlk3.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "cr.mm"
include "crp.mm"
include "cz.mm"
include "nn0zd.mm"
include "peano2zm.mm"
include "zre.mm"
include "3syl.mm"
include "simpl3.mm"
include "clwwlknonfin.mm"
include "hashcl.mm"
include "nn0red.mm"
include "remulcld.mm"
include "prmm2nn0.mm"
include "reexpcld.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "modaddabs.mm"
include "eqcomd.mm"
include "syl.mm"
include "cc0.mm"
include "cn.mm"
include "nn0z.mm"
include "mulmoddvds.mm"
include "simpr2.mm"
include "jca.mm"
include "powm2modprm.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "clt.mm"
include "nnred.mm"
include "prmgt1.mm"
include "1mod.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "pm2.61ine.mm"

theorem numclwwlk5
  let cP: class P
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cN: class N
  let vx: setvar x
  assume numclwwlk3.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph /\ V e. Fin ) /\ ( X e. V /\ P e. Prime /\ P || ( K - 1 ) ) ) -> ( ( # ` ( X ( ClWWalksNOn ` G ) P ) ) mod P ) = 1 )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    w3a
    #
    cX
    cV
    wcel
    #
    cP
    cprime
    wcel
    #
    cP
    cK
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    w3a
    #
    wa
    #
    cX
    cP
    cG
    cclwwlknon
    cfv
    #
    co
    #
    chash
    cfv
    #
    cP
    cmo
    co
    #
    c1
    wceq
    #
    wi
    cP
    c2
    cP
    c2
    wceq
    #
    @3
    @4
    c2
    cprime
    wcel
    #
    c2
    @6
    cdvds
    wbr
    #
    w3a
    #
    wa
    #
    cX
    c2
    @10
    co
    #
    chash
    cfv
    #
    c2
    cmo
    co
    #
    c1
    wceq
    #
    @9
    @14
    @19
    @23
    wi
    @15
    @19
    @0
    @4
    cK
    cn0
    wcel
    #
    w3a
    @17
    @23
    @19
    @0
    @4
    @24
    @0
    @1
    @2
    @18
    simpl1
    @3
    @4
    @16
    @17
    simpr1
    @18
    @3
    @24
    @4
    @16
    @3
    @24
    wi
    #
    @17
    @4
    @3
    @24
    @4
    @3
    wa
    cG
    cfusgr
    wcel
    #
    @0
    cV
    c0
    wne
    #
    @24
    @3
    @26
    @4
    @0
    @2
    @26
    @1
    cG
    cK
    cV
    numclwwlk3.v
    finrusgrfusgr
    3adant2
    adantl
    @4
    @0
    @1
    @2
    simpr1
    @4
    @27
    @3
    cV
    cX
    ne0i
    adantr
    cG
    cK
    cV
    numclwwlk3.v
    frusgrnn0
    syl3anc
    ex
    #
    3ad2ant1
    impcom
    3jca
    @3
    @4
    @16
    @17
    simpr3
    cG
    cK
    cV
    cX
    numclwwlk3.v
    numclwwlk5lem
    sylc
    a1i
    @15
    @8
    @18
    @3
    @15
    @5
    @16
    @7
    @17
    @4
    cP
    c2
    cprime
    eleq1
    cP
    c2
    @6
    cdvds
    breq1
    3anbi23d
    anbi2d
    @15
    @13
    @22
    c1
    @15
    @12
    @21
    cP
    c2
    cmo
    @15
    @11
    @20
    chash
    cP
    c2
    cX
    @10
    oveq2
    fveq2d
    @15
    id
    oveq12d
    eqeq1d
    3imtr4d
    cP
    c2
    wne
    #
    @9
    @14
    @29
    @9
    wa
    #
    @13
    @6
    cX
    cP
    c2
    cmin
    co
    #
    @10
    co
    #
    chash
    cfv
    #
    cmul
    co
    #
    cK
    @31
    cexp
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    @34
    cP
    cmo
    co
    #
    @35
    cP
    cmo
    co
    #
    caddc
    co
    #
    cP
    cmo
    co
    #
    c1
    @30
    @12
    @36
    cP
    cmo
    @30
    @0
    @1
    wa
    #
    @2
    @4
    cP
    c3
    cuz
    cfv
    wcel
    #
    @12
    @36
    wceq
    @9
    @42
    @29
    @3
    @42
    @8
    @0
    @1
    @2
    3simpa
    adantr
    adantl
    @0
    @1
    @2
    @8
    @29
    simprl3
    @4
    @5
    @7
    @3
    @29
    simprr1
    @9
    @29
    @43
    @8
    @29
    @43
    wi
    #
    @3
    @5
    @4
    @44
    @7
    @5
    @29
    @43
    @5
    @29
    wa
    cP
    cprime
    c2
    csn
    cdif
    wcel
    @43
    cP
    cprime
    c2
    eldifsn
    cP
    oddprmge3
    sylbir
    ex
    3ad2ant2
    adantl
    impcom
    cG
    cK
    cP
    cV
    cX
    numclwwlk3.v
    numclwwlk3
    syl13anc
    oveq1d
    @30
    @34
    cr
    wcel
    #
    @35
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    w3a
    #
    @37
    @41
    wceq
    @9
    @48
    @29
    @9
    @45
    @46
    @47
    @9
    @6
    @33
    @9
    cK
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @6
    cr
    wcel
    @9
    cK
    @8
    @3
    @24
    @4
    @5
    @25
    @7
    @28
    3ad2ant1
    impcom
    #
    nn0zd
    #
    cK
    peano2zm
    #
    @6
    zre
    3syl
    @9
    @33
    @9
    @2
    @32
    cfn
    wcel
    @33
    cn0
    wcel
    @0
    @1
    @2
    @8
    simpl3
    cG
    @31
    cV
    cX
    numclwwlk3.v
    clwwlknonfin
    @32
    hashcl
    3syl
    #
    nn0red
    remulcld
    @9
    cK
    @31
    @9
    cK
    @51
    nn0red
    @8
    @31
    cn0
    wcel
    #
    @3
    @5
    @4
    @55
    @7
    cP
    prmm2nn0
    3ad2ant2
    adantl
    reexpcld
    @8
    @47
    @3
    @5
    @4
    @47
    @7
    @5
    cP
    cP
    prmnn
    #
    nnrpd
    3ad2ant2
    adantl
    3jca
    adantl
    @48
    @41
    @37
    @34
    @35
    cP
    modaddabs
    eqcomd
    syl
    @9
    @41
    c1
    wceq
    @29
    @9
    @41
    cc0
    c1
    caddc
    co
    #
    cP
    cmo
    co
    #
    c1
    @9
    @40
    @57
    cP
    cmo
    @9
    @38
    cc0
    @39
    c1
    caddc
    @9
    cP
    cn
    wcel
    #
    @50
    @33
    cz
    wcel
    #
    w3a
    @7
    @38
    cc0
    wceq
    @9
    @59
    @50
    @60
    @8
    @59
    @3
    @5
    @4
    @59
    @7
    @56
    3ad2ant2
    adantl
    @9
    @24
    @49
    @50
    @51
    cK
    nn0z
    @53
    3syl
    @9
    @33
    @54
    nn0zd
    3jca
    @3
    @4
    @5
    @7
    simpr3
    #
    @6
    @33
    cP
    mulmoddvds
    sylc
    @9
    @5
    @49
    wa
    @7
    @39
    c1
    wceq
    @9
    @5
    @49
    @3
    @4
    @5
    @7
    simpr2
    @52
    jca
    @61
    cK
    cP
    powm2modprm
    sylc
    oveq12d
    oveq1d
    @8
    @58
    c1
    wceq
    #
    @3
    @5
    @4
    @62
    @7
    @5
    @58
    c1
    cP
    cmo
    co
    #
    c1
    @57
    c1
    cP
    cmo
    0p1e1
    oveq1i
    @5
    cP
    cr
    wcel
    c1
    cP
    clt
    wbr
    @63
    c1
    wceq
    @5
    cP
    @56
    nnred
    cP
    prmgt1
    cP
    1mod
    syl2anc
    syl5eq
    3ad2ant2
    adantl
    eqtrd
    adantl
    3eqtrd
    ex
    pm2.61ine
end
