include "co.mm"
include "caddc.mm"
include "cxr.mm"
include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "xrsxmet.mm"
include "a1i.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcld.mm"
include "rpred.mm"
include "clt.mm"
include "rpxrd.mm"
include "xmetrtri2.mm"
include "syl13anc.mm"
include "xrlelttrd.mm"
include "wi.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "xmetlecl.mm"
include "syl122anc.mm"
include "wceq.mm"
include "xmetsym.mm"
include "oveq12d.mm"
include "eqbrtrd.mm"
include "readdcld.mm"
include "cxad.mm"
include "xmettri.mm"
include "rexadd.mm"
include "breqtrd.mm"
include "lt2halvesd.mm"
include "lelttrd.mm"

theorem metdcnlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xmetdcn2.1: |- J = ( MetOpen ` D )
  assume xmetdcn2.2: |- C = ( dist ` RR*s )
  assume xmetdcn2.3: |- K = ( MetOpen ` C )
  assume metdcn.d: |- ( ph -> D e. ( *Met ` X ) )
  assume metdcn.a: |- ( ph -> A e. X )
  assume metdcn.b: |- ( ph -> B e. X )
  assume metdcn.r: |- ( ph -> R e. RR+ )
  assume metdcn.y: |- ( ph -> Y e. X )
  assume metdcn.z: |- ( ph -> Z e. X )
  assume metdcn.4: |- ( ph -> ( A D Y ) < ( R / 2 ) )
  assume metdcn.5: |- ( ph -> ( B D Z ) < ( R / 2 ) )


  assert |- ( ph -> ( ( A D B ) C ( Y D Z ) ) < R )

  proof
    wph
    cA
    cB
    cD
    co
    #
    cY
    cZ
    cD
    co
    #
    cC
    co
    #
    @0
    cY
    cB
    cD
    co
    #
    cC
    co
    #
    @3
    @1
    cC
    co
    #
    caddc
    co
    #
    cR
    wph
    cC
    cxr
    cxmt
    cfv
    wcel
    #
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @6
    cr
    wcel
    @2
    @6
    cle
    wbr
    @2
    cr
    wcel
    @7
    wph
    cC
    xmetdcn2.2
    xrsxmet
    a1i
    #
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @8
    metdcn.d
    metdcn.a
    metdcn.b
    cA
    cB
    cD
    cX
    xmetcl
    syl3anc
    #
    wph
    @11
    cY
    cX
    wcel
    #
    cZ
    cX
    wcel
    #
    @9
    metdcn.d
    metdcn.y
    metdcn.z
    cY
    cZ
    cD
    cX
    xmetcl
    syl3anc
    #
    wph
    @4
    @5
    wph
    @7
    @8
    @3
    cxr
    wcel
    #
    cR
    c2
    cdiv
    co
    #
    cr
    wcel
    #
    @4
    @19
    cle
    wbr
    #
    @4
    cr
    wcel
    #
    @10
    @14
    wph
    @11
    @15
    @13
    @18
    metdcn.d
    metdcn.y
    metdcn.b
    cY
    cB
    cD
    cX
    xmetcl
    syl3anc
    #
    wph
    @19
    wph
    cR
    metdcn.r
    rphalfcld
    #
    rpred
    #
    wph
    @4
    @19
    clt
    wbr
    #
    @21
    wph
    @4
    cA
    cY
    cD
    co
    #
    @19
    wph
    @7
    @8
    @18
    @4
    cxr
    wcel
    #
    @10
    @14
    @23
    @0
    @3
    cC
    cxr
    xmetcl
    syl3anc
    #
    wph
    @11
    @12
    @15
    @27
    cxr
    wcel
    metdcn.d
    metdcn.a
    metdcn.y
    cA
    cY
    cD
    cX
    xmetcl
    syl3anc
    wph
    @19
    @24
    rpxrd
    #
    wph
    @11
    @12
    @15
    @13
    @4
    @27
    cle
    wbr
    metdcn.d
    metdcn.a
    metdcn.y
    metdcn.b
    cA
    cY
    cB
    cD
    cC
    cX
    xmetdcn2.2
    xmetrtri2
    syl13anc
    metdcn.4
    xrlelttrd
    #
    wph
    @28
    @19
    cxr
    wcel
    #
    @26
    @21
    wi
    @29
    @30
    @4
    @19
    xrltle
    syl2anc
    mpd
    @0
    @3
    @19
    cC
    cxr
    xmetlecl
    syl122anc
    #
    wph
    @7
    @18
    @9
    @20
    @5
    @19
    cle
    wbr
    #
    @5
    cr
    wcel
    #
    @10
    @23
    @17
    @25
    wph
    @5
    @19
    clt
    wbr
    #
    @34
    wph
    @5
    cB
    cZ
    cD
    co
    #
    @19
    wph
    @7
    @18
    @9
    @5
    cxr
    wcel
    #
    @10
    @23
    @17
    @3
    @1
    cC
    cxr
    xmetcl
    syl3anc
    #
    wph
    @11
    @13
    @16
    @37
    cxr
    wcel
    metdcn.d
    metdcn.b
    metdcn.z
    cB
    cZ
    cD
    cX
    xmetcl
    syl3anc
    @30
    wph
    @5
    cB
    cY
    cD
    co
    #
    cZ
    cY
    cD
    co
    #
    cC
    co
    #
    @37
    cle
    wph
    @3
    @40
    @1
    @41
    cC
    wph
    @11
    @15
    @13
    @3
    @40
    wceq
    metdcn.d
    metdcn.y
    metdcn.b
    cY
    cB
    cD
    cX
    xmetsym
    syl3anc
    wph
    @11
    @15
    @16
    @1
    @41
    wceq
    metdcn.d
    metdcn.y
    metdcn.z
    cY
    cZ
    cD
    cX
    xmetsym
    syl3anc
    oveq12d
    wph
    @11
    @13
    @16
    @15
    @42
    @37
    cle
    wbr
    metdcn.d
    metdcn.b
    metdcn.z
    metdcn.y
    cB
    cZ
    cY
    cD
    cC
    cX
    xmetdcn2.2
    xmetrtri2
    syl13anc
    eqbrtrd
    metdcn.5
    xrlelttrd
    #
    wph
    @38
    @32
    @36
    @34
    wi
    @39
    @30
    @5
    @19
    xrltle
    syl2anc
    mpd
    @3
    @1
    @19
    cC
    cxr
    xmetlecl
    syl122anc
    #
    readdcld
    #
    wph
    @2
    @4
    @5
    cxad
    co
    #
    @6
    cle
    wph
    @7
    @8
    @9
    @18
    @2
    @46
    cle
    wbr
    @10
    @14
    @17
    @23
    @0
    @1
    @3
    cC
    cxr
    xmettri
    syl13anc
    wph
    @22
    @35
    @46
    @6
    wceq
    @33
    @44
    @4
    @5
    rexadd
    syl2anc
    breqtrd
    #
    @0
    @1
    @6
    cC
    cxr
    xmetlecl
    syl122anc
    @45
    wph
    cR
    metdcn.r
    rpred
    #
    @47
    wph
    @4
    @5
    cR
    @33
    @44
    @48
    @31
    @43
    lt2halvesd
    lelttrd
end
