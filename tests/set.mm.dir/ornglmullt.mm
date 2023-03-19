include "co.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "eqid.mm"
include "corng.mm"
include "wcel.mm"
include "w3a.mm"
include "pltle.mm"
include "imp.mm"
include "syl31anc.mm"
include "crg.mm"
include "cgrp.mm"
include "orngring.mm"
include "syl.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "ornglmulle.mm"
include "wceq.mm"
include "wa.mm"
include "cinvr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "cur.mm"
include "cui.mm"
include "cdr.mm"
include "pltne.mm"
include "necomd.mm"
include "drngunit.mm"
include "biimpar.mm"
include "syl12anc.mm"
include "unitlinv.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "ringinvcl.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "3eqtr3d.mm"
include "adantr.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "wb.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "pltval.mm"
include "mpbir2and.mm"

theorem ornglmullt
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.lt: class .<
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume ornglmullt.b: |- B = ( Base ` R )
  assume ornglmullt.t: |- .x. = ( .r ` R )
  assume ornglmullt.0: |- .0. = ( 0g ` R )
  assume ornglmullt.1: |- ( ph -> R e. oRing )
  assume ornglmullt.2: |- ( ph -> X e. B )
  assume ornglmullt.3: |- ( ph -> Y e. B )
  assume ornglmullt.4: |- ( ph -> Z e. B )
  assume ornglmullt.l: |- .< = ( lt ` R )
  assume ornglmullt.d: |- ( ph -> R e. DivRing )
  assume ornglmullt.5: |- ( ph -> X .< Y )
  assume ornglmullt.6: |- ( ph -> .0. .< Z )


  assert |- ( ph -> ( Z .x. X ) .< ( Z .x. Y ) )

  proof
    wph
    cZ
    cX
    c.x
    co
    #
    cZ
    cY
    c.x
    co
    #
    c.lt
    wbr
    #
    @0
    @1
    cR
    cple
    cfv
    #
    wbr
    #
    @0
    @1
    wne
    #
    wph
    cB
    cR
    c.x
    @3
    cX
    cY
    c.0
    cZ
    ornglmullt.b
    ornglmullt.t
    ornglmullt.0
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.4
    @3
    eqid
    #
    wph
    cR
    corng
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.lt
    wbr
    #
    cX
    cY
    @3
    wbr
    #
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.5
    @7
    @8
    @9
    w3a
    #
    @10
    @11
    corng
    cB
    cB
    c.lt
    cR
    @3
    cX
    cY
    @6
    ornglmullt.l
    pltle
    imp
    syl31anc
    wph
    @7
    c.0
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    c.0
    cZ
    c.lt
    wbr
    #
    c.0
    cZ
    @3
    wbr
    #
    ornglmullt.1
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    @13
    wph
    @7
    @17
    ornglmullt.1
    cR
    orngring
    syl
    #
    cR
    ringgrp
    cB
    cR
    c.0
    ornglmullt.b
    ornglmullt.0
    grpidcl
    3syl
    #
    ornglmullt.4
    ornglmullt.6
    @7
    @13
    @14
    w3a
    #
    @15
    @16
    corng
    cB
    cB
    c.lt
    cR
    @3
    c.0
    cZ
    @6
    ornglmullt.l
    pltle
    imp
    syl31anc
    ornglmulle
    wph
    @0
    @1
    wph
    @0
    @1
    wceq
    #
    cX
    cY
    wceq
    wph
    @21
    wa
    #
    cZ
    cR
    cinvr
    cfv
    #
    cfv
    #
    @0
    c.x
    co
    #
    @24
    @1
    c.x
    co
    #
    cX
    cY
    @22
    @0
    @1
    @24
    c.x
    wph
    @21
    simpr
    oveq2d
    wph
    @25
    cX
    wceq
    @21
    wph
    @24
    cZ
    c.x
    co
    #
    cX
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cX
    c.x
    co
    #
    @25
    cX
    wph
    @27
    @29
    cX
    c.x
    wph
    @17
    cZ
    cR
    cui
    cfv
    #
    wcel
    #
    @27
    @29
    wceq
    @18
    wph
    cR
    cdr
    wcel
    #
    @14
    cZ
    c.0
    wne
    #
    @32
    ornglmullt.d
    ornglmullt.4
    wph
    c.0
    cZ
    wph
    @7
    @13
    @14
    @15
    c.0
    cZ
    wne
    #
    ornglmullt.1
    @19
    ornglmullt.4
    ornglmullt.6
    @20
    @15
    @35
    corng
    cB
    cB
    c.lt
    cR
    c.0
    cZ
    ornglmullt.l
    pltne
    imp
    syl31anc
    necomd
    @33
    @32
    @14
    @34
    wa
    cB
    cR
    @31
    cZ
    c.0
    ornglmullt.b
    @31
    eqid
    #
    ornglmullt.0
    drngunit
    biimpar
    syl12anc
    #
    cR
    c.x
    @31
    @29
    @23
    cZ
    @36
    @23
    eqid
    #
    ornglmullt.t
    @29
    eqid
    #
    unitlinv
    syl2anc
    #
    oveq1d
    wph
    @17
    @24
    cB
    wcel
    #
    @14
    @8
    @28
    @25
    wceq
    @18
    wph
    @17
    @32
    @41
    @18
    @37
    cB
    cR
    @31
    @23
    cZ
    @36
    @38
    ornglmullt.b
    ringinvcl
    syl2anc
    #
    ornglmullt.4
    ornglmullt.2
    cB
    cR
    c.x
    @24
    cZ
    cX
    ornglmullt.b
    ornglmullt.t
    ringass
    syl13anc
    wph
    @17
    @8
    @30
    cX
    wceq
    @18
    ornglmullt.2
    cB
    cR
    c.x
    @29
    cX
    ornglmullt.b
    ornglmullt.t
    @39
    ringlidm
    syl2anc
    3eqtr3d
    adantr
    wph
    @26
    cY
    wceq
    @21
    wph
    @27
    cY
    c.x
    co
    #
    @29
    cY
    c.x
    co
    #
    @26
    cY
    wph
    @27
    @29
    cY
    c.x
    @40
    oveq1d
    wph
    @17
    @41
    @14
    @9
    @43
    @26
    wceq
    @18
    @42
    ornglmullt.4
    ornglmullt.3
    cB
    cR
    c.x
    @24
    cZ
    cY
    ornglmullt.b
    ornglmullt.t
    ringass
    syl13anc
    wph
    @17
    @9
    @44
    cY
    wceq
    @18
    ornglmullt.3
    cB
    cR
    c.x
    @29
    cY
    ornglmullt.b
    ornglmullt.t
    @39
    ringlidm
    syl2anc
    3eqtr3d
    adantr
    3eqtr3d
    @22
    cX
    cY
    wph
    cX
    cY
    wne
    #
    @21
    wph
    @7
    @8
    @9
    @10
    @45
    ornglmullt.1
    ornglmullt.2
    ornglmullt.3
    ornglmullt.5
    @12
    @10
    @45
    corng
    cB
    cB
    c.lt
    cR
    cX
    cY
    ornglmullt.l
    pltne
    imp
    syl31anc
    adantr
    neneqd
    pm2.65da
    neqned
    wph
    @7
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @2
    @4
    @5
    wa
    wb
    ornglmullt.1
    wph
    @17
    @14
    @8
    @46
    @18
    ornglmullt.4
    ornglmullt.2
    cB
    cR
    c.x
    cZ
    cX
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    wph
    @17
    @14
    @9
    @47
    @18
    ornglmullt.4
    ornglmullt.3
    cB
    cR
    c.x
    cZ
    cY
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    corng
    cB
    cB
    c.lt
    cR
    @3
    @0
    @1
    @6
    ornglmullt.l
    pltval
    syl3anc
    mpbir2and
end
