include "cs3.mm"
include "ccgra.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ccgrg.mm"
include "w3a.mm"
include "wrex.mm"
include "cds.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simprlr.mm"
include "tgcgrcomlr.mm"
include "eqcomd.mm"
include "simprrr.mm"
include "simplr.mm"
include "clng.mm"
include "simprll.mm"
include "hlln.mm"
include "orcd.mm"
include "colrot1.mm"
include "cleg.mm"
include "wne.mm"
include "wo.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp3d.mm"
include "orcomd.mm"
include "simprrl.mm"
include "tgcgrsub2.mm"
include "trgcgr.mm"
include "axtgcgrrflx.mm"
include "tgfscgr.mm"
include "3jca.mm"
include "wb.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "trgcgrg.mm"
include "3expa.mm"
include "adantr.mm"
include "mpbird.mm"
include "necomd.mm"
include "hlcgrex.mm"
include "reeanv.mm"
include "sylanbrc.mm"
include "reximddv2.mm"
include "iscgra.mm"

theorem cgraswap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume cgraid.p: |- P = ( Base ` G )
  assume cgraid.i: |- I = ( Itv ` G )
  assume cgraid.g: |- ( ph -> G e. TarskiG )
  assume cgraid.k: |- K = ( hlG ` G )
  assume cgraid.a: |- ( ph -> A e. P )
  assume cgraid.b: |- ( ph -> B e. P )
  assume cgraid.c: |- ( ph -> C e. P )
  assume cgraid.1: |- ( ph -> A =/= B )
  assume cgraid.2: |- ( ph -> B =/= C )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" C B A "> )

  proof
    wph
    cA
    cB
    cC
    cs3
    #
    cC
    cB
    cA
    cs3
    cG
    ccgra
    cfv
    wbr
    @0
    vx
    cv
    #
    cB
    vy
    cv
    #
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    @1
    cC
    cB
    cK
    cfv
    #
    wbr
    #
    @2
    cA
    @5
    wbr
    #
    w3a
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    wph
    @6
    cB
    @1
    cG
    cds
    cfv
    #
    co
    cB
    cA
    @9
    co
    wceq
    #
    wa
    #
    @7
    cB
    @2
    @9
    co
    #
    cB
    cC
    @9
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    @8
    vx
    vy
    cP
    cP
    wph
    @1
    cP
    wcel
    #
    wa
    #
    @2
    cP
    wcel
    #
    wa
    #
    @16
    wa
    #
    @4
    @6
    @7
    @21
    @4
    cA
    cB
    @9
    co
    #
    @1
    cB
    @9
    co
    #
    wceq
    #
    @13
    @12
    wceq
    #
    cC
    cA
    @9
    co
    #
    @2
    @1
    @9
    co
    #
    wceq
    #
    w3a
    #
    @21
    @24
    @25
    @28
    @21
    @23
    @22
    @21
    cB
    @1
    cB
    cA
    cP
    cG
    cI
    @9
    cgraid.p
    @9
    eqid
    #
    cgraid.i
    wph
    cG
    cstrkg
    wcel
    #
    @17
    @19
    @16
    cgraid.g
    ad3antrrr
    #
    wph
    cB
    cP
    wcel
    #
    @17
    @19
    @16
    cgraid.b
    ad3antrrr
    #
    wph
    @17
    @19
    @16
    simpllr
    #
    @34
    wph
    cA
    cP
    wcel
    #
    @17
    @19
    @16
    cgraid.a
    ad3antrrr
    #
    @20
    @6
    @10
    @15
    simprlr
    #
    tgcgrcomlr
    #
    eqcomd
    @21
    @12
    @13
    @20
    @11
    @7
    @14
    simprrr
    #
    eqcomd
    #
    @21
    @27
    @26
    @21
    @1
    @2
    cA
    cC
    cP
    cG
    cI
    @9
    cgraid.p
    @30
    cgraid.i
    @32
    @35
    @18
    @19
    @16
    simplr
    #
    @37
    wph
    cC
    cP
    wcel
    #
    @17
    @19
    @16
    cgraid.c
    ad3antrrr
    #
    @21
    cB
    @2
    cA
    cC
    cP
    @3
    @2
    cG
    cI
    cG
    clng
    cfv
    #
    @9
    cB
    cC
    @1
    cgraid.p
    @45
    eqid
    #
    cgraid.i
    @32
    @34
    @44
    @35
    @3
    eqid
    #
    @34
    @42
    @30
    @42
    @37
    @44
    @21
    cP
    cG
    cI
    @45
    cC
    cB
    @1
    cgraid.p
    @46
    cgraid.i
    @32
    @44
    @34
    @35
    @21
    @1
    cC
    cB
    @45
    co
    wcel
    cC
    cB
    wceq
    @21
    @1
    cC
    cB
    cP
    cG
    cI
    cK
    @45
    cgraid.p
    cgraid.i
    cgraid.k
    @35
    @44
    @34
    @32
    @46
    @20
    @6
    @10
    @15
    simprll
    #
    hlln
    orcd
    colrot1
    @21
    cB
    cC
    @1
    cB
    cP
    @3
    @2
    cA
    cG
    @9
    cgraid.p
    @30
    @47
    @32
    @34
    @44
    @35
    @34
    @42
    @37
    @41
    @21
    cB
    cC
    @1
    cB
    cP
    @2
    cA
    cG
    cI
    cG
    cleg
    cfv
    #
    @9
    cgraid.p
    @30
    cgraid.i
    @49
    eqid
    @32
    @34
    @44
    @35
    @34
    @34
    @42
    @37
    @21
    @1
    cB
    cC
    cI
    co
    wcel
    #
    cC
    cB
    @1
    cI
    co
    wcel
    #
    @21
    @1
    cB
    wne
    #
    cC
    cB
    wne
    #
    @50
    @51
    wo
    #
    @21
    @6
    @52
    @53
    @54
    w3a
    @48
    @21
    @1
    cC
    cB
    cP
    cG
    cI
    cK
    cstrkg
    cgraid.p
    cgraid.i
    cgraid.k
    @35
    @44
    @34
    @32
    ishlg
    mpbid
    simp3d
    orcomd
    @21
    @2
    cB
    wne
    #
    cA
    cB
    wne
    #
    @2
    cB
    cA
    cI
    co
    wcel
    cA
    cB
    @2
    cI
    co
    wcel
    wo
    #
    @21
    @7
    @55
    @56
    @57
    w3a
    @20
    @11
    @7
    @14
    simprrl
    #
    @21
    @2
    cA
    cB
    cP
    cG
    cI
    cK
    cstrkg
    cgraid.p
    cgraid.i
    cgraid.k
    @42
    @37
    @34
    @32
    ishlg
    mpbid
    simp3d
    @41
    @38
    tgcgrsub2
    @39
    trgcgr
    @40
    @21
    cP
    cG
    cI
    @9
    cC
    @2
    cgraid.p
    @30
    cgraid.i
    @32
    @44
    @42
    axtgcgrrflx
    wph
    cB
    cC
    wne
    @17
    @19
    @16
    cgraid.2
    ad3antrrr
    tgfscgr
    tgcgrcomlr
    eqcomd
    3jca
    @20
    @4
    @29
    wb
    #
    @16
    wph
    @17
    @19
    @59
    wph
    @17
    @19
    w3a
    cA
    cB
    cC
    @1
    cP
    @3
    cB
    @2
    cG
    @9
    cgraid.p
    @30
    @47
    wph
    @17
    @31
    @19
    cgraid.g
    3ad2ant1
    wph
    @17
    @36
    @19
    cgraid.a
    3ad2ant1
    wph
    @17
    @33
    @19
    cgraid.b
    3ad2ant1
    #
    wph
    @17
    @43
    @19
    cgraid.c
    3ad2ant1
    wph
    @17
    @19
    simp2
    @60
    wph
    @17
    @19
    simp3
    trgcgrg
    3expa
    adantr
    mpbird
    @48
    @58
    3jca
    wph
    @11
    vx
    cP
    wrex
    @15
    vy
    cP
    wrex
    @16
    vy
    cP
    wrex
    vx
    cP
    wrex
    wph
    vx
    cB
    cB
    cA
    cC
    cP
    cG
    cI
    cK
    @9
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.b
    cgraid.b
    cgraid.a
    cgraid.g
    cgraid.c
    @30
    wph
    cB
    cC
    cgraid.2
    necomd
    wph
    cA
    cB
    cgraid.1
    necomd
    hlcgrex
    wph
    vy
    cB
    cB
    cC
    cA
    cP
    cG
    cI
    cK
    @9
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.b
    cgraid.b
    cgraid.c
    cgraid.g
    cgraid.a
    @30
    cgraid.1
    cgraid.2
    hlcgrex
    @11
    @15
    vx
    vy
    cP
    cP
    reeanv
    sylanbrc
    reximddv2
    wph
    vx
    vy
    cA
    cB
    cC
    cC
    cP
    cB
    cA
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgraid.c
    cgraid.b
    cgraid.a
    iscgra
    mpbird
end
