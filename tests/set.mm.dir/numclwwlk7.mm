include "crusgr.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "cprime.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "w3a.mm"
include "cclwwlkn.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "3jca.mm"
include "numclwwlk6.mm"
include "stoic3.mm"
include "cmul.mm"
include "caddc.mm"
include "simp2.mm"
include "ancomd.mm"
include "simp1.mm"
include "frrusgrord.mm"
include "sylc.mm"
include "oveq1d.mm"
include "cn0.mm"
include "numclwwlk7lem.mm"
include "cc0.mm"
include "nn0cn.mm"
include "cc.mm"
include "peano2cnm.mm"
include "syl.mm"
include "mulcomd.mm"
include "adantr.mm"
include "cn.mm"
include "cz.mm"
include "prmnn.mm"
include "ad2antrl.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "mulmoddvds.mm"
include "eqtrd.mm"
include "cr.mm"
include "clt.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "1mod.mm"
include "oveq12d.mm"
include "crp.mm"
include "nn0re.mm"
include "peano2rem.mm"
include "remulcld.mm"
include "1red.mm"
include "nnrpd.mm"
include "modaddabs.mm"
include "syl3anc.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"

theorem numclwwlk7
  let cP: class P
  let cG: class G
  let cK: class K
  let cV: class V
  let vx: setvar x
  assume numclwwlk6.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph ) /\ ( V =/= (/) /\ V e. Fin ) /\ ( P e. Prime /\ P || ( K - 1 ) ) ) -> ( ( # ` ( P ClWWalksN G ) ) mod P ) = 1 )

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
    wa
    #
    cV
    c0
    wne
    #
    cV
    cfn
    wcel
    #
    wa
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
    wa
    #
    w3a
    #
    cP
    cG
    cclwwlkn
    co
    chash
    cfv
    cP
    cmo
    co
    #
    cV
    chash
    cfv
    #
    cP
    cmo
    co
    #
    c1
    @2
    @5
    @0
    @1
    @4
    w3a
    @9
    @11
    @13
    wceq
    @2
    @5
    wa
    @0
    @1
    @4
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprr
    3jca
    cP
    cG
    cK
    cV
    numclwwlk6.v
    numclwwlk6
    stoic3
    @10
    @13
    cK
    @7
    cmul
    co
    #
    c1
    caddc
    co
    #
    cP
    cmo
    co
    #
    c1
    @10
    @12
    @15
    cP
    cmo
    @10
    @4
    @3
    wa
    @1
    @0
    wa
    @12
    @15
    wceq
    @10
    @3
    @4
    @2
    @5
    @9
    simp2
    ancomd
    @10
    @0
    @1
    @2
    @5
    @9
    simp1
    ancomd
    cG
    cK
    cV
    numclwwlk6.v
    frrusgrord
    sylc
    oveq1d
    @2
    @5
    cK
    cn0
    wcel
    #
    @9
    @16
    c1
    wceq
    cG
    cK
    cV
    numclwwlk6.v
    numclwwlk7lem
    @17
    @9
    wa
    #
    @14
    cP
    cmo
    co
    #
    c1
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
    cc0
    c1
    caddc
    co
    #
    cP
    cmo
    co
    #
    @16
    c1
    @18
    @21
    @23
    cP
    cmo
    @18
    @19
    cc0
    @20
    c1
    caddc
    @18
    @19
    @7
    cK
    cmul
    co
    #
    cP
    cmo
    co
    #
    cc0
    @17
    @19
    @26
    wceq
    @9
    @17
    @14
    @25
    cP
    cmo
    @17
    cK
    @7
    cK
    nn0cn
    #
    @17
    cK
    cc
    wcel
    @7
    cc
    wcel
    @27
    cK
    peano2cnm
    syl
    mulcomd
    oveq1d
    adantr
    @18
    cP
    cn
    wcel
    #
    @7
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    @8
    @26
    cc0
    wceq
    @18
    @28
    @29
    @30
    @6
    @28
    @17
    @8
    cP
    prmnn
    #
    ad2antrl
    @17
    @29
    @9
    @17
    @30
    @29
    cK
    nn0z
    #
    cK
    peano2zm
    syl
    adantr
    @17
    @30
    @9
    @32
    adantr
    3jca
    @17
    @6
    @8
    simprr
    @7
    cK
    cP
    mulmoddvds
    sylc
    eqtrd
    @18
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @20
    c1
    wceq
    #
    @6
    @35
    @17
    @8
    @6
    @33
    @34
    @6
    cP
    @31
    nnred
    #
    cP
    prmgt1
    #
    jca
    ad2antrl
    cP
    1mod
    #
    syl
    oveq12d
    oveq1d
    @18
    @14
    cr
    wcel
    #
    c1
    cr
    wcel
    cP
    crp
    wcel
    #
    @22
    @16
    wceq
    @17
    @40
    @9
    @17
    cK
    @7
    cK
    nn0re
    #
    @17
    cK
    cr
    wcel
    @7
    cr
    wcel
    @42
    cK
    peano2rem
    syl
    remulcld
    adantr
    @18
    1red
    @6
    @41
    @17
    @8
    @6
    cP
    @31
    nnrpd
    ad2antrl
    @14
    c1
    cP
    modaddabs
    syl3anc
    @18
    @24
    @20
    c1
    @23
    c1
    cP
    cmo
    0p1e1
    oveq1i
    @6
    @36
    @17
    @8
    @6
    @33
    @34
    @36
    @37
    @38
    @39
    syl2anc
    ad2antrl
    syl5eq
    3eqtr3d
    stoic3
    eqtrd
    eqtrd
end
