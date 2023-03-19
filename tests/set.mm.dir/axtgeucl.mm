include "co.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cvv.mm"
include "cstrkge.mm"
include "wa.mm"
include "istrkge.mm"
include "sylib.mm"
include "simprd.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "3anbi12d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "2ralbidv.mm"
include "3anbi2d.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "oveq2.mm"
include "rspc3v.mm"
include "syl3anc.mm"
include "mpd.mm"
include "neeq2.mm"
include "3anbi123d.mm"
include "imbi1d.mm"
include "3anbi3d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mp3and.mm"

theorem axtgeucl
  let wph: wff ph
  let cP: class P
  let cU: class U
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume axtrkge.p: |- P = ( Base ` G )
  assume axtrkge.d: |- .- = ( dist ` G )
  assume axtrkge.i: |- I = ( Itv ` G )
  assume axtgeucl.g: |- ( ph -> G e. TarskiGE )
  assume axtgeucl.1: |- ( ph -> X e. P )
  assume axtgeucl.2: |- ( ph -> Y e. P )
  assume axtgeucl.3: |- ( ph -> Z e. P )
  assume axtgeucl.4: |- ( ph -> U e. P )
  assume axtgeucl.5: |- ( ph -> V e. P )
  assume axtgeucl.6: |- ( ph -> U e. ( X I V ) )
  assume axtgeucl.7: |- ( ph -> U e. ( Y I Z ) )
  assume axtgeucl.8: |- ( ph -> X =/= U )

  disjoint a b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint V a
  disjoint V b
  disjoint U a
  disjoint U b
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  disjoint Z a
  disjoint Z b
  disjoint .- a
  disjoint .- b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint V v
  disjoint U u
  disjoint U v
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y y
  disjoint Y z
  disjoint Z u
  disjoint Z v
  disjoint Z z
  disjoint .- u
  disjoint .- v
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint I u
  disjoint I v
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint P z
  assert |- ( ph -> E. a e. P E. b e. P ( Y e. ( X I a ) /\ Z e. ( X I b ) /\ V e. ( a I b ) ) )

  proof
    wph
    cU
    cX
    cV
    cI
    co
    #
    wcel
    #
    cU
    cY
    cZ
    cI
    co
    #
    wcel
    #
    cX
    cU
    wne
    #
    cY
    cX
    va
    cv
    #
    cI
    co
    #
    wcel
    #
    cZ
    cX
    vb
    cv
    #
    cI
    co
    #
    wcel
    #
    cV
    @5
    @8
    cI
    co
    #
    wcel
    #
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    axtgeucl.6
    axtgeucl.7
    axtgeucl.8
    wph
    vu
    cv
    #
    cX
    vv
    cv
    #
    cI
    co
    #
    wcel
    #
    @15
    @2
    wcel
    #
    cX
    @15
    wne
    #
    w3a
    #
    @7
    @10
    @16
    @11
    wcel
    #
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    #
    @1
    @3
    @4
    w3a
    #
    @14
    wi
    #
    wph
    @15
    vx
    cv
    #
    @16
    cI
    co
    #
    wcel
    #
    @15
    vy
    cv
    #
    vz
    cv
    #
    cI
    co
    #
    wcel
    #
    @29
    @15
    wne
    #
    w3a
    #
    @32
    @29
    @5
    cI
    co
    #
    wcel
    #
    @33
    @29
    @8
    cI
    co
    #
    wcel
    #
    @22
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    #
    vz
    cP
    wral
    vy
    cP
    wral
    vx
    cP
    wral
    #
    @26
    wph
    cG
    cvv
    wcel
    #
    @46
    wph
    cG
    cstrkge
    wcel
    @47
    @46
    wa
    axtgeucl.g
    vx
    vy
    vz
    vv
    vu
    cP
    cG
    cI
    c.mi
    va
    vb
    axtrkge.p
    axtrkge.d
    axtrkge.i
    istrkge
    sylib
    simprd
    wph
    cX
    cP
    wcel
    cY
    cP
    wcel
    cZ
    cP
    wcel
    @46
    @26
    wi
    axtgeucl.1
    axtgeucl.2
    axtgeucl.3
    @45
    @26
    @18
    @35
    @20
    w3a
    #
    @32
    @6
    wcel
    #
    @33
    @9
    wcel
    #
    @22
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    @18
    @15
    cY
    @33
    cI
    co
    #
    wcel
    #
    @20
    w3a
    #
    @7
    @50
    @22
    w3a
    #
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    wi
    #
    vv
    cP
    wral
    vu
    cP
    wral
    vx
    vy
    vz
    cX
    cY
    cZ
    cP
    cP
    cP
    @29
    cX
    wceq
    #
    @44
    @53
    vu
    vv
    cP
    cP
    @60
    @37
    @48
    @43
    @52
    @60
    @31
    @18
    @36
    @20
    @35
    @60
    @30
    @17
    @15
    @29
    cX
    @16
    cI
    oveq1
    eleq2d
    @29
    cX
    @15
    neeq1
    3anbi13d
    @60
    @42
    @51
    va
    vb
    cP
    cP
    @60
    @39
    @49
    @41
    @50
    @22
    @60
    @38
    @6
    @32
    @29
    cX
    @5
    cI
    oveq1
    eleq2d
    @60
    @40
    @9
    @33
    @29
    cX
    @8
    cI
    oveq1
    eleq2d
    3anbi12d
    2rexbidv
    imbi12d
    2ralbidv
    @32
    cY
    wceq
    #
    @53
    @59
    vu
    vv
    cP
    cP
    @61
    @48
    @56
    @52
    @58
    @61
    @35
    @55
    @18
    @20
    @61
    @34
    @54
    @15
    @32
    cY
    @33
    cI
    oveq1
    eleq2d
    3anbi2d
    @61
    @51
    @57
    va
    vb
    cP
    cP
    @61
    @49
    @7
    @50
    @22
    @32
    cY
    @6
    eleq1
    3anbi1d
    2rexbidv
    imbi12d
    2ralbidv
    @33
    cZ
    wceq
    #
    @59
    @25
    vu
    vv
    cP
    cP
    @62
    @56
    @21
    @58
    @24
    @62
    @55
    @19
    @18
    @20
    @62
    @54
    @2
    @15
    @33
    cZ
    cY
    cI
    oveq2
    eleq2d
    3anbi2d
    @62
    @57
    @23
    va
    vb
    cP
    cP
    @62
    @50
    @10
    @7
    @22
    @33
    cZ
    @9
    eleq1
    3anbi2d
    2rexbidv
    imbi12d
    2ralbidv
    rspc3v
    syl3anc
    mpd
    wph
    cU
    cP
    wcel
    cV
    cP
    wcel
    @26
    @28
    wi
    axtgeucl.4
    axtgeucl.5
    @25
    @28
    cU
    @17
    wcel
    #
    @3
    @4
    w3a
    #
    @24
    wi
    vu
    vv
    cU
    cV
    cP
    cP
    @15
    cU
    wceq
    #
    @21
    @64
    @24
    @65
    @18
    @63
    @19
    @3
    @20
    @4
    @15
    cU
    @17
    eleq1
    @15
    cU
    @2
    eleq1
    @15
    cU
    cX
    neeq2
    3anbi123d
    imbi1d
    @16
    cV
    wceq
    #
    @64
    @27
    @24
    @14
    @66
    @63
    @1
    @3
    @4
    @66
    @17
    @0
    cU
    @16
    cV
    cX
    cI
    oveq2
    eleq2d
    3anbi1d
    @66
    @23
    @13
    va
    vb
    cP
    cP
    @66
    @22
    @12
    @7
    @10
    @16
    cV
    @11
    eleq1
    3anbi3d
    2rexbidv
    imbi12d
    rspc2v
    syl2anc
    mpd
    mp3and
end
