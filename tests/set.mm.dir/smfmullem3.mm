include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cioo.mm"
include "wcel.mm"
include "cq.mm"
include "wrex.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "c3.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "crp.mm"
include "wceq.mm"
include "a1i.mm"
include "1rp.mm"
include "cmul.mm"
include "cabs.mm"
include "caddc.mm"
include "cdiv.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "remulcld.mm"
include "difrp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "1re.mm"
include "recnd.mm"
include "abscld.mm"
include "readdcld.mm"
include "0re.mm"
include "rpgt0d.mm"
include "0red.mm"
include "absge0d.mm"
include "addge01d.mm"
include "letrd.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "rpdivcld.mm"
include "eqeltrd.mm"
include "ifcld.mm"
include "rpred.mm"
include "resubcld.mm"
include "rexrd.mm"
include "ltsubrpd.mm"
include "qelioo.mm"
include "ltaddrpd.mm"
include "ad2antrr.mm"
include "simp-4l.mm"
include "syl.mm"
include "ad8antr.mm"
include "simp-8r.mm"
include "simp-6r.mm"
include "simp-4r.mm"
include "simplr.mm"
include "simp-7r.mm"
include "simp-5r.mm"
include "simpllr.mm"
include "simpr.mm"
include "smfmullem2.mm"
include "ex.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem smfmullem3
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let cR: class R
  let cU: class U
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume smfmullem3.r: |- ( ph -> R e. RR )
  assume smfmullem3.k: |- K = { q e. ( QQ ^m ( 0 ... 3 ) ) | A. u e. ( ( q ` 0 ) (,) ( q ` 1 ) ) A. v e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ( u x. v ) < R }
  assume smfmullem3.u: |- ( ph -> U e. RR )
  assume smfmullem3.v: |- ( ph -> V e. RR )
  assume smfmullem3.l: |- ( ph -> ( U x. V ) < R )
  assume smfmullem3.x: |- X = ( ( R - ( U x. V ) ) / ( 1 + ( ( abs ` U ) + ( abs ` V ) ) ) )
  assume smfmullem3.y: |- Y = if ( 1 <_ X , 1 , X )

  disjoint R q
  disjoint U q
  disjoint U u
  disjoint U v
  disjoint q u
  disjoint q v
  disjoint u v
  disjoint V q
  disjoint V u
  disjoint V v
  disjoint Y u
  disjoint Y v
  disjoint ph u
  disjoint ph v
  disjoint K p
  disjoint K r
  disjoint K s
  disjoint K z
  disjoint p r
  disjoint p s
  disjoint p z
  disjoint r s
  disjoint r z
  disjoint s z
  disjoint U p
  disjoint U r
  disjoint U s
  disjoint U z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint q r
  disjoint q s
  disjoint q z
  disjoint r u
  disjoint r v
  disjoint s u
  disjoint s v
  disjoint u z
  disjoint v z
  disjoint V p
  disjoint V r
  disjoint V s
  disjoint V z
  disjoint Y p
  disjoint Y r
  disjoint Y s
  disjoint Y z
  disjoint p ph
  disjoint ph r
  disjoint ph s
  disjoint ph z
  disjoint k x
  assert |- ( ph -> E. q e. K ( U e. ( ( q ` 0 ) (,) ( q ` 1 ) ) /\ V e. ( ( q ` 2 ) (,) ( q ` 3 ) ) ) )

  proof
    wph
    vp
    cv
    #
    cU
    cY
    cmin
    co
    #
    cU
    cioo
    co
    wcel
    #
    vp
    cq
    wrex
    cU
    cc0
    vq
    cv
    #
    cfv
    c1
    @3
    cfv
    cioo
    co
    wcel
    cV
    c2
    @3
    cfv
    c3
    @3
    cfv
    cioo
    co
    wcel
    wa
    vq
    cK
    wrex
    #
    wph
    vp
    @1
    cU
    wph
    @1
    wph
    cU
    cY
    smfmullem3.u
    wph
    cY
    wph
    cY
    c1
    cX
    cle
    wbr
    #
    c1
    cX
    cif
    #
    crp
    cY
    @6
    wceq
    wph
    smfmullem3.y
    a1i
    wph
    @5
    c1
    cX
    crp
    c1
    crp
    wcel
    wph
    1rp
    a1i
    #
    wph
    cX
    cR
    cU
    cV
    cmul
    co
    #
    cmin
    co
    #
    c1
    cU
    cabs
    cfv
    #
    cV
    cabs
    cfv
    #
    caddc
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    crp
    cX
    @14
    wceq
    wph
    smfmullem3.x
    a1i
    wph
    @9
    @13
    wph
    @8
    cR
    clt
    wbr
    #
    @9
    crp
    wcel
    #
    smfmullem3.l
    wph
    @8
    cr
    wcel
    cR
    cr
    wcel
    #
    @15
    @16
    wb
    wph
    cU
    cV
    smfmullem3.u
    smfmullem3.v
    remulcld
    smfmullem3.r
    @8
    cR
    difrp
    syl2anc
    mpbid
    wph
    @13
    wph
    c1
    @12
    c1
    cr
    wcel
    wph
    1re
    a1i
    #
    wph
    @10
    @11
    wph
    cU
    wph
    cU
    smfmullem3.u
    recnd
    #
    abscld
    #
    wph
    cV
    wph
    cV
    smfmullem3.v
    recnd
    #
    abscld
    #
    readdcld
    #
    readdcld
    #
    wph
    cc0
    c1
    @13
    cc0
    cr
    wcel
    wph
    0re
    a1i
    @18
    @24
    wph
    c1
    @7
    rpgt0d
    wph
    cc0
    @12
    cle
    wbr
    c1
    @13
    cle
    wbr
    wph
    cc0
    @10
    @12
    wph
    0red
    @20
    @23
    wph
    cU
    @19
    absge0d
    wph
    cc0
    @11
    cle
    wbr
    @10
    @12
    cle
    wbr
    wph
    cV
    @21
    absge0d
    wph
    @10
    @11
    @20
    @22
    addge01d
    mpbid
    letrd
    wph
    c1
    @12
    @18
    @23
    addge01d
    mpbid
    ltletrd
    elrpd
    rpdivcld
    eqeltrd
    ifcld
    eqeltrd
    #
    rpred
    #
    resubcld
    rexrd
    wph
    cU
    smfmullem3.u
    rexrd
    #
    wph
    cU
    cY
    smfmullem3.u
    @25
    ltsubrpd
    qelioo
    wph
    @2
    @4
    vp
    cq
    wph
    @0
    cq
    wcel
    #
    wa
    #
    @2
    @4
    @29
    @2
    wa
    #
    vr
    cv
    #
    cU
    cU
    cY
    caddc
    co
    #
    cioo
    co
    wcel
    #
    vr
    cq
    wrex
    #
    @4
    wph
    @34
    @28
    @2
    wph
    vr
    cU
    @32
    @27
    wph
    @32
    wph
    cU
    cY
    smfmullem3.u
    @26
    readdcld
    rexrd
    wph
    cU
    cY
    smfmullem3.u
    @25
    ltaddrpd
    qelioo
    ad2antrr
    @30
    @33
    @4
    vr
    cq
    @30
    @31
    cq
    wcel
    #
    wa
    #
    @33
    @4
    @36
    @33
    wa
    #
    vs
    cv
    #
    cV
    cY
    cmin
    co
    #
    cV
    cioo
    co
    wcel
    #
    vs
    cq
    wrex
    #
    @4
    @37
    wph
    @41
    wph
    @28
    @2
    @35
    @33
    simp-4l
    #
    wph
    vs
    @39
    cV
    wph
    @39
    wph
    cV
    cY
    smfmullem3.v
    @26
    resubcld
    rexrd
    wph
    cV
    smfmullem3.v
    rexrd
    #
    wph
    cV
    cY
    smfmullem3.v
    @25
    ltsubrpd
    qelioo
    syl
    @37
    @40
    @4
    vs
    cq
    @37
    @38
    cq
    wcel
    #
    wa
    #
    @40
    @4
    @45
    @40
    wa
    #
    vz
    cv
    #
    cV
    cV
    cY
    caddc
    co
    #
    cioo
    co
    wcel
    #
    vz
    cq
    wrex
    #
    @4
    @46
    wph
    @50
    @37
    wph
    @44
    @40
    @42
    ad2antrr
    wph
    vz
    cV
    @48
    @43
    wph
    @48
    wph
    cV
    cY
    smfmullem3.v
    @26
    readdcld
    rexrd
    wph
    cV
    cY
    smfmullem3.v
    @25
    ltaddrpd
    qelioo
    syl
    @46
    @49
    @4
    vz
    cq
    @46
    @47
    cq
    wcel
    #
    wa
    #
    @49
    @4
    @52
    @49
    wa
    vv
    vu
    cR
    @0
    @31
    @38
    cU
    cK
    cV
    cX
    cY
    @47
    vq
    wph
    @17
    @28
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    smfmullem3.r
    ad8antr
    smfmullem3.k
    wph
    cU
    cr
    wcel
    @28
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    smfmullem3.u
    ad8antr
    wph
    cV
    cr
    wcel
    @28
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    smfmullem3.v
    ad8antr
    wph
    @15
    @28
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    smfmullem3.l
    ad8antr
    wph
    @28
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    simp-8r
    @30
    @35
    @33
    @44
    @40
    @51
    @49
    simp-6r
    @37
    @44
    @40
    @51
    @49
    simp-4r
    @46
    @51
    @49
    simplr
    @29
    @2
    @35
    @33
    @44
    @40
    @51
    @49
    simp-7r
    @36
    @33
    @44
    @40
    @51
    @49
    simp-5r
    @45
    @40
    @51
    @49
    simpllr
    @52
    @49
    simpr
    smfmullem3.x
    smfmullem3.y
    smfmullem2
    ex
    rexlimdva
    mpd
    ex
    rexlimdva
    mpd
    ex
    rexlimdva
    mpd
    ex
    rexlimdva
    mpd
end
