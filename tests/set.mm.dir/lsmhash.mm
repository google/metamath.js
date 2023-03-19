include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cxp.mm"
include "cmul.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "cpj1.mm"
include "cop.mm"
include "c1st.mm"
include "c2nd.mm"
include "cplusg.mm"
include "ovexd.mm"
include "csubg.mm"
include "wcel.mm"
include "cvv.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wa.mm"
include "eqid.mm"
include "pj1f.mm"
include "ffvelrnda.mm"
include "pj2f.mm"
include "opelxpi.mm"
include "ex.mm"
include "jca.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "lsmelvali.mm"
include "syl2an.mm"
include "wb.mm"
include "adantr.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "simprl.mm"
include "ad2antll.mm"
include "pj1eq.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "syl6bb.mm"
include "eqop.mm"
include "bitr4d.mm"
include "en3d.mm"
include "hasheni.mm"
include "syl.mm"
include "cfn.mm"
include "hashxp.mm"
include "eqtrd.mm"

theorem lsmhash
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume lsmhash.p: |- .(+) = ( LSSum ` G )
  assume lsmhash.o: |- .0. = ( 0g ` G )
  assume lsmhash.z: |- Z = ( Cntz ` G )
  assume lsmhash.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmhash.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmhash.i: |- ( ph -> ( T i^i U ) = { .0. } )
  assume lsmhash.s: |- ( ph -> T C_ ( Z ` U ) )
  assume lsmhash.1: |- ( ph -> T e. Fin )
  assume lsmhash.2: |- ( ph -> U e. Fin )


  assert |- ( ph -> ( # ` ( T .(+) U ) ) = ( ( # ` T ) x. ( # ` U ) ) )

  proof
    wph
    cT
    cU
    c.po
    co
    #
    chash
    cfv
    #
    cT
    cU
    cxp
    #
    chash
    cfv
    #
    cT
    chash
    cfv
    cU
    chash
    cfv
    cmul
    co
    #
    wph
    @0
    @2
    cen
    wbr
    @1
    @3
    wceq
    wph
    vx
    vy
    @0
    @2
    vx
    cv
    #
    cT
    cU
    cG
    cpj1
    cfv
    #
    co
    #
    cfv
    #
    @5
    cU
    cT
    @6
    co
    #
    cfv
    #
    cop
    #
    vy
    cv
    #
    c1st
    cfv
    #
    @12
    c2nd
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wph
    cT
    cU
    c.po
    ovexd
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @17
    wcel
    #
    @2
    cvv
    wcel
    lsmhash.t
    lsmhash.u
    cT
    cU
    @17
    @17
    xpexg
    syl2anc
    wph
    @5
    @0
    wcel
    #
    @11
    @2
    wcel
    #
    wph
    @20
    wa
    @8
    cT
    wcel
    @10
    cU
    wcel
    @21
    wph
    @0
    cT
    @5
    @7
    wph
    @6
    @15
    c.po
    cT
    cU
    cG
    c.0
    cZ
    @15
    eqid
    #
    lsmhash.p
    lsmhash.o
    lsmhash.z
    lsmhash.t
    lsmhash.u
    lsmhash.i
    lsmhash.s
    @6
    eqid
    #
    pj1f
    ffvelrnda
    wph
    @0
    cU
    @5
    @9
    wph
    @6
    @15
    c.po
    cT
    cU
    cG
    c.0
    cZ
    @22
    lsmhash.p
    lsmhash.o
    lsmhash.z
    lsmhash.t
    lsmhash.u
    lsmhash.i
    lsmhash.s
    @23
    pj2f
    ffvelrnda
    @8
    @10
    cT
    cU
    opelxpi
    syl2anc
    ex
    wph
    @12
    @2
    wcel
    #
    @16
    @0
    wcel
    #
    wph
    @18
    @19
    wa
    @13
    cT
    wcel
    #
    @14
    cU
    wcel
    #
    wa
    @25
    @24
    wph
    @18
    @19
    lsmhash.t
    lsmhash.u
    jca
    @24
    @26
    @27
    @12
    cT
    cU
    xp1st
    #
    @12
    cT
    cU
    xp2nd
    #
    jca
    @15
    c.po
    cT
    cU
    cG
    @13
    @14
    @22
    lsmhash.p
    lsmelvali
    syl2an
    ex
    wph
    @20
    @24
    wa
    #
    @5
    @16
    wceq
    #
    @12
    @11
    wceq
    #
    wb
    wph
    @30
    wa
    #
    @31
    @13
    @8
    wceq
    #
    @14
    @10
    wceq
    #
    wa
    #
    @32
    @33
    @31
    @8
    @13
    wceq
    #
    @10
    @14
    wceq
    #
    wa
    @36
    @33
    @13
    @14
    @6
    @15
    c.po
    cT
    cU
    cG
    @5
    c.0
    cZ
    @22
    lsmhash.p
    lsmhash.o
    lsmhash.z
    wph
    @18
    @30
    lsmhash.t
    adantr
    wph
    @19
    @30
    lsmhash.u
    adantr
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @30
    lsmhash.i
    adantr
    wph
    cT
    cU
    cZ
    cfv
    wss
    @30
    lsmhash.s
    adantr
    @23
    wph
    @20
    @24
    simprl
    @24
    @26
    wph
    @20
    @28
    ad2antll
    @24
    @27
    wph
    @20
    @29
    ad2antll
    pj1eq
    @37
    @34
    @38
    @35
    @8
    @13
    eqcom
    @10
    @14
    eqcom
    anbi12i
    syl6bb
    @24
    @32
    @36
    wb
    wph
    @20
    @12
    @8
    @10
    cT
    cU
    eqop
    ad2antll
    bitr4d
    ex
    en3d
    @0
    @2
    hasheni
    syl
    wph
    cT
    cfn
    wcel
    cU
    cfn
    wcel
    @3
    @4
    wceq
    lsmhash.1
    lsmhash.2
    cT
    cU
    hashxp
    syl2anc
    eqtrd
end
