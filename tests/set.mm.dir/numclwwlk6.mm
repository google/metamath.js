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
include "cclwwlkn.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cv.mm"
include "cclwwlknon.mm"
include "csu.mm"
include "cfusgr.mm"
include "cn.mm"
include "wceq.mm"
include "finrusgrfusgr.mm"
include "3adant2.mm"
include "prmnn.mm"
include "adantr.mm"
include "numclwwlk4.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simp3.mm"
include "cz.mm"
include "cn0.mm"
include "clwwlknonfin.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0zd.mm"
include "ralrimiva.mm"
include "modfsummod.mm"
include "simpl.mm"
include "simpr.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3anass.mm"
include "sylibr.mm"
include "numclwwlk5.mm"
include "syl2an2r.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "cmul.mm"
include "cc.mm"
include "1cnd.mm"
include "fsumconst.mm"
include "cr.mm"
include "nn0red.mm"
include "ax-1rid.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "3eqtrd.mm"

theorem numclwwlk6
  let cP: class P
  let cG: class G
  let cK: class K
  let cV: class V
  let vx: setvar x
  assume numclwwlk6.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph /\ V e. Fin ) /\ ( P e. Prime /\ P || ( K - 1 ) ) ) -> ( ( # ` ( P ClWWalksN G ) ) mod P ) = ( ( # ` V ) mod P ) )

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
    cP
    cprime
    wcel
    #
    cP
    cK
    c1
    cmin
    co
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    cP
    cG
    cclwwlkn
    co
    chash
    cfv
    #
    cP
    cmo
    co
    cV
    vx
    cv
    #
    cP
    cG
    cclwwlknon
    cfv
    co
    #
    chash
    cfv
    #
    vx
    csu
    #
    cP
    cmo
    co
    #
    cV
    c1
    vx
    csu
    #
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
    @7
    @8
    @12
    cP
    cmo
    @3
    cG
    cfusgr
    wcel
    #
    cP
    cn
    wcel
    #
    @8
    @12
    wceq
    @6
    @0
    @2
    @17
    @1
    cG
    cK
    cV
    numclwwlk6.v
    finrusgrfusgr
    3adant2
    @4
    @18
    @5
    cP
    prmnn
    adantr
    #
    vx
    cG
    cP
    cV
    numclwwlk6.v
    numclwwlk4
    syl2an
    oveq1d
    @7
    @13
    cV
    @11
    cP
    cmo
    co
    #
    vx
    csu
    #
    cP
    cmo
    co
    @15
    @7
    cV
    @11
    vx
    cP
    @6
    @18
    @3
    @19
    adantl
    @3
    @2
    @6
    @0
    @1
    @2
    simp3
    #
    adantr
    #
    @7
    @11
    cz
    wcel
    vx
    cV
    @7
    @9
    cV
    wcel
    #
    wa
    #
    @11
    @25
    @2
    @10
    cfn
    wcel
    @11
    cn0
    wcel
    @7
    @2
    @24
    @23
    adantr
    cG
    cP
    cV
    @9
    numclwwlk6.v
    clwwlknonfin
    @10
    hashcl
    3syl
    nn0zd
    ralrimiva
    modfsummod
    @7
    @21
    @14
    cP
    cmo
    @7
    cV
    @20
    c1
    vx
    @7
    @3
    @24
    @24
    @4
    @5
    w3a
    #
    @20
    c1
    wceq
    @3
    @6
    simpl
    @25
    @24
    @6
    wa
    @26
    @25
    @6
    @24
    @7
    @6
    @24
    @3
    @6
    simpr
    anim1i
    ancomd
    @24
    @4
    @5
    3anass
    sylibr
    cP
    cG
    cK
    cV
    @9
    numclwwlk6.v
    numclwwlk5
    syl2an2r
    sumeq2dv
    oveq1d
    eqtrd
    @7
    @14
    @16
    cP
    cmo
    @7
    @14
    @16
    c1
    cmul
    co
    #
    @16
    @3
    @2
    c1
    cc
    wcel
    @14
    @27
    wceq
    @6
    @22
    @6
    1cnd
    cV
    c1
    vx
    fsumconst
    syl2an
    @3
    @27
    @16
    wceq
    #
    @6
    @2
    @0
    @28
    @1
    @2
    @16
    cr
    wcel
    @28
    @2
    @16
    cV
    hashcl
    nn0red
    @16
    ax-1rid
    syl
    3ad2ant3
    adantr
    eqtrd
    oveq1d
    3eqtrd
end
