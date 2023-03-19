include "cv.mm"
include "ccid.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cop.mm"
include "wral.mm"
include "wa.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "csubc.mm"
include "eqid.mm"
include "ccat.mm"
include "subcrcl.mm"
include "syl.mm"
include "issubc2.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"
include "ad4antr.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "opeq12d.mm"
include "simpr.mm"
include "oveq123d.mm"
include "eleq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "adantld.mm"
include "mpd.mm"

theorem subccocl
  let wph: wff ph
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.1: class .1.
  assume subcidcl.j: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcidcl.2: |- ( ph -> J Fn ( S X. S ) )
  assume subcidcl.x: |- ( ph -> X e. S )
  assume subccocl.o: |- .x. = ( comp ` C )
  assume subccocl.y: |- ( ph -> Y e. S )
  assume subccocl.z: |- ( ph -> Z e. S )
  assume subccocl.f: |- ( ph -> F e. ( X J Y ) )
  assume subccocl.g: |- ( ph -> G e. ( Y J Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X J Z ) )

  proof
    wph
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    @0
    @0
    cJ
    co
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    @0
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    c.x
    co
    #
    co
    #
    @0
    @7
    cJ
    co
    #
    wcel
    #
    vg
    @5
    @7
    cJ
    co
    #
    wral
    #
    vf
    @0
    @5
    cJ
    co
    #
    wral
    #
    vz
    cS
    wral
    #
    vy
    cS
    wral
    #
    wa
    #
    vx
    cS
    wral
    #
    cG
    cF
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    #
    co
    #
    cX
    cZ
    cJ
    co
    #
    wcel
    #
    wph
    cJ
    cC
    chomf
    cfv
    #
    cssc
    wbr
    #
    @19
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    @26
    @19
    wa
    subcidcl.j
    wph
    vx
    vy
    vz
    cC
    cS
    c.x
    @1
    vf
    vg
    @25
    cJ
    @25
    eqid
    @1
    eqid
    subccocl.o
    wph
    @27
    cC
    ccat
    wcel
    subcidcl.j
    cC
    cJ
    subcrcl
    syl
    subcidcl.2
    issubc2
    mpbid
    simprd
    wph
    @18
    @24
    vx
    cX
    cS
    subcidcl.x
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @17
    @24
    @2
    @29
    @16
    @24
    vy
    cY
    cS
    wph
    cY
    cS
    wcel
    @28
    subccocl.y
    adantr
    @29
    @5
    cY
    wceq
    #
    wa
    #
    @15
    @24
    vz
    cZ
    cS
    wph
    cZ
    cS
    wcel
    @28
    @30
    subccocl.z
    ad2antrr
    @31
    @7
    cZ
    wceq
    #
    wa
    #
    @13
    @24
    vf
    cF
    @14
    @33
    cF
    cX
    cY
    cJ
    co
    #
    @14
    wph
    cF
    @34
    wcel
    @28
    @30
    @32
    subccocl.f
    ad3antrrr
    @33
    @0
    cX
    @5
    cY
    cJ
    wph
    @28
    @30
    @32
    simpllr
    @29
    @30
    @32
    simplr
    oveq12d
    eleqtrrd
    @33
    @4
    cF
    wceq
    #
    wa
    #
    @11
    @24
    vg
    cG
    @12
    @36
    cG
    cY
    cZ
    cJ
    co
    #
    @12
    wph
    cG
    @37
    wcel
    @28
    @30
    @32
    @35
    subccocl.g
    ad4antr
    @36
    @5
    cY
    @7
    cZ
    cJ
    @29
    @30
    @32
    @35
    simpllr
    @31
    @32
    @35
    simplr
    oveq12d
    eleqtrrd
    @36
    @3
    cG
    wceq
    #
    wa
    #
    @9
    @22
    @10
    @23
    @39
    @3
    cG
    @4
    cF
    @8
    @21
    @39
    @6
    @20
    @7
    cZ
    c.x
    @39
    @0
    cX
    @5
    cY
    wph
    @28
    @30
    @32
    @35
    @38
    simp-5r
    #
    @29
    @30
    @32
    @35
    @38
    simp-4r
    opeq12d
    @31
    @32
    @35
    @38
    simpllr
    #
    oveq12d
    @36
    @38
    simpr
    @33
    @35
    @38
    simplr
    oveq123d
    @39
    @0
    cX
    @7
    cZ
    cJ
    @40
    @41
    oveq12d
    eleq12d
    rspcdv
    rspcimdv
    rspcimdv
    rspcimdv
    adantld
    rspcimdv
    mpd
end
