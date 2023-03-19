include "cv.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "eeanv.mm"
include "2rexbii.mm"
include "reeanv.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "wcel.mm"
include "w3a.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "simp2l.mm"
include "sseldi.mm"
include "zred.mm"
include "simp2r.mm"
include "cle.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simp3ll.mm"
include "adantr.mm"
include "simp3rl.mm"
include "simp3lr.mm"
include "simp3rr.mm"
include "cc.mm"
include "simpl1.mm"
include "sylan.mm"
include "simpr.mm"
include "co.mm"
include "wceq.mm"
include "ntrivcvgmullem.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "lecasei.mm"
include "3expia.mm"
include "exlimdvv.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem ntrivcvgmul
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vp: setvar p
  assume ntrivcvgmul.1: |- Z = ( ZZ>= ` M )
  assume ntrivcvgmul.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume ntrivcvgmul.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume ntrivcvgmul.5: |- ( ph -> E. m e. Z E. z ( z =/= 0 /\ seq m ( x. , G ) ~~> z ) )
  assume ntrivcvgmul.6: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume ntrivcvgmul.7: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) x. ( G ` k ) ) )

  disjoint F m
  disjoint F z
  disjoint G n
  disjoint G y
  disjoint H m
  disjoint H n
  disjoint H y
  disjoint H z
  disjoint m n
  disjoint m p
  disjoint m ph
  disjoint m w
  disjoint m y
  disjoint m z
  disjoint n p
  disjoint n ph
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint p y
  disjoint p z
  disjoint ph y
  disjoint ph z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint Z m
  disjoint Z n
  disjoint Z y
  disjoint Z z
  disjoint F w
  disjoint G w
  disjoint H p
  disjoint H w
  disjoint p w
  disjoint Z p
  disjoint F k
  disjoint G k
  disjoint H k
  disjoint k m
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint k z
  disjoint Z k
  assert |- ( ph -> E. p e. Z E. w ( w =/= 0 /\ seq p ( x. , H ) ~~> w ) )

  proof
    wph
    vy
    cv
    #
    cc0
    wne
    #
    cmul
    cF
    vn
    cv
    #
    cseq
    @0
    cli
    wbr
    #
    wa
    #
    vz
    cv
    #
    cc0
    wne
    #
    cmul
    cG
    vm
    cv
    #
    cseq
    @5
    cli
    wbr
    #
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    #
    vm
    cZ
    wrex
    vn
    cZ
    wrex
    #
    vw
    cv
    #
    cc0
    wne
    cmul
    cH
    vp
    cv
    cseq
    @13
    cli
    wbr
    wa
    vw
    wex
    vp
    cZ
    wrex
    #
    wph
    @4
    vy
    wex
    #
    vn
    cZ
    wrex
    #
    @9
    vz
    wex
    #
    vm
    cZ
    wrex
    #
    @12
    ntrivcvgmul.3
    ntrivcvgmul.5
    @12
    @15
    @17
    wa
    #
    vm
    cZ
    wrex
    vn
    cZ
    wrex
    @16
    @18
    wa
    @11
    @19
    vn
    vm
    cZ
    cZ
    @4
    @9
    vy
    vz
    eeanv
    2rexbii
    @15
    @17
    vn
    vm
    cZ
    cZ
    reeanv
    bitri
    sylanbrc
    wph
    @11
    @14
    vn
    vm
    cZ
    cZ
    wph
    @2
    cZ
    wcel
    #
    @7
    cZ
    wcel
    #
    wa
    #
    wa
    @10
    @14
    vy
    vz
    wph
    @22
    @10
    @14
    wph
    @22
    @10
    w3a
    #
    @14
    @2
    @7
    @23
    @2
    @23
    cZ
    cz
    @2
    cZ
    cM
    cuz
    cfv
    cz
    ntrivcvgmul.1
    cM
    uzssz
    eqsstri
    #
    wph
    @20
    @21
    @10
    simp2l
    sseldi
    zred
    @23
    @7
    @23
    cZ
    cz
    @7
    @24
    wph
    @20
    @21
    @10
    simp2r
    sseldi
    zred
    @23
    @2
    @7
    cle
    wbr
    #
    wa
    #
    vw
    @7
    vk
    cF
    cG
    cH
    cM
    @2
    @0
    @5
    cZ
    vp
    ntrivcvgmul.1
    @20
    @21
    wph
    @10
    @25
    simpl2l
    @20
    @21
    wph
    @10
    @25
    simpl2r
    @23
    @1
    @25
    @1
    @3
    @9
    wph
    @22
    simp3ll
    #
    adantr
    @23
    @6
    @25
    @6
    @8
    @4
    wph
    @22
    simp3rl
    #
    adantr
    @23
    @3
    @25
    @1
    @3
    @9
    wph
    @22
    simp3lr
    #
    adantr
    @23
    @8
    @25
    @6
    @8
    @4
    wph
    @22
    simp3rr
    #
    adantr
    @26
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @31
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    @22
    @10
    @25
    simpl1
    #
    ntrivcvgmul.4
    sylan
    @26
    wph
    @32
    @31
    cG
    cfv
    #
    cc
    wcel
    #
    @35
    ntrivcvgmul.6
    sylan
    @23
    @25
    simpr
    @26
    wph
    @32
    @31
    cH
    cfv
    #
    @33
    @36
    cmul
    co
    #
    wceq
    @35
    ntrivcvgmul.7
    sylan
    ntrivcvgmullem
    @23
    @7
    @2
    cle
    wbr
    #
    wa
    #
    vw
    @2
    vk
    cG
    cF
    cH
    cM
    @7
    @5
    @0
    cZ
    vp
    ntrivcvgmul.1
    @20
    @21
    wph
    @10
    @40
    simpl2r
    @20
    @21
    wph
    @10
    @40
    simpl2l
    @23
    @6
    @40
    @28
    adantr
    @23
    @1
    @40
    @27
    adantr
    @23
    @8
    @40
    @30
    adantr
    @23
    @3
    @40
    @29
    adantr
    @41
    wph
    @32
    @37
    wph
    @22
    @10
    @40
    simpl1
    #
    ntrivcvgmul.6
    sylan
    @41
    wph
    @32
    @34
    @42
    ntrivcvgmul.4
    sylan
    @23
    @40
    simpr
    @41
    wph
    @32
    @38
    @36
    @33
    cmul
    co
    #
    wceq
    @42
    wph
    @32
    wa
    #
    @38
    @39
    @43
    ntrivcvgmul.7
    @44
    @33
    @36
    ntrivcvgmul.4
    ntrivcvgmul.6
    mulcomd
    eqtrd
    sylan
    ntrivcvgmullem
    lecasei
    3expia
    exlimdvv
    rexlimdvva
    mpd
end
