include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "wa.mm"
include "eqeq2.mm"
include "csb.mm"
include "simplr.mm"
include "wsbc.mm"
include "simpll.mm"
include "simpr.mm"
include "sbceq1a.mm"
include "biimpd.mm"
include "sylc.mm"
include "wi.mm"
include "dfsbcq.mm"
include "csbeq1.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "wcel.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "syl.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "eqcomd.mm"
include "a1d.mm"
include "wn.mm"
include "pm3.24.mm"
include "wb.mm"
include "sbcieg.mm"
include "anbi1d.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "imp.mm"
include "anass1rs.mm"
include "ex.mm"
include "ifbothda.mm"
include "csbeq1a.mm"
include "biimprd.mm"
include "notbid.mm"
include "nsyld.mm"
include "anim2d.mm"
include "mtoi.mm"
include "expdimp.mm"

theorem ifeqeqx
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume ifeqeqx.1: |- ( x = X -> A = C )
  assume ifeqeqx.2: |- ( x = Y -> B = a )
  assume ifeqeqx.3: |- ( x = X -> ( ch <-> th ) )
  assume ifeqeqx.4: |- ( x = Y -> ( ch <-> ps ) )
  assume ifeqeqx.5: |- ( ph -> a = C )
  assume ifeqeqx.6: |- ( ( ph /\ ps ) -> th )
  assume ifeqeqx.y: |- ( ph -> Y e. V )
  assume ifeqeqx.x: |- ( ph -> X e. W )

  disjoint a x
  disjoint C x
  disjoint X x
  disjoint Y x
  disjoint V x
  disjoint W x
  disjoint ps x
  disjoint th x
  assert |- ( ( ph /\ x = if ( ps , X , Y ) ) -> a = if ( ch , A , B ) )

  proof
    wch
    va
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    #
    @0
    wch
    cA
    cB
    cif
    #
    wceq
    wph
    vx
    cv
    wps
    cX
    cY
    cif
    #
    wceq
    #
    wa
    #
    cA
    cB
    cA
    @3
    @0
    eqeq2
    cB
    @3
    @0
    eqeq2
    @6
    wch
    wa
    #
    @5
    @0
    vx
    @4
    cA
    csb
    #
    wceq
    #
    @1
    wph
    @5
    wch
    simplr
    #
    @7
    wph
    wch
    vx
    @4
    wsbc
    #
    @9
    wph
    @5
    wch
    simpll
    @7
    @5
    wch
    @11
    @10
    @6
    wch
    simpr
    @5
    wch
    @11
    wch
    vx
    @4
    sbceq1a
    #
    biimpd
    sylc
    wps
    wch
    vx
    cX
    wsbc
    #
    @0
    vx
    cX
    cA
    csb
    #
    wceq
    #
    wi
    wch
    vx
    cY
    wsbc
    #
    @0
    vx
    cY
    cA
    csb
    #
    wceq
    #
    wi
    @11
    @9
    wi
    wph
    cX
    cY
    cX
    @4
    wceq
    #
    @13
    @11
    @15
    @9
    wch
    vx
    cX
    @4
    dfsbcq
    #
    @19
    @14
    @8
    @0
    vx
    cX
    @4
    cA
    csbeq1
    eqeq2d
    imbi12d
    cY
    @4
    wceq
    #
    @16
    @11
    @18
    @9
    wch
    vx
    cY
    @4
    dfsbcq
    #
    @21
    @17
    @8
    @0
    vx
    cY
    @4
    cA
    csbeq1
    eqeq2d
    imbi12d
    wph
    wps
    wa
    #
    @15
    @13
    @23
    @14
    @0
    wph
    @14
    @0
    wceq
    wps
    wph
    @14
    cC
    @0
    wph
    cX
    cW
    wcel
    #
    @14
    cC
    wceq
    ifeqeqx.x
    vx
    cX
    cA
    cC
    cW
    @24
    vx
    cC
    nfcvd
    ifeqeqx.1
    csbiegf
    syl
    ifeqeqx.5
    eqtr4d
    adantr
    eqcomd
    a1d
    wph
    wps
    wn
    #
    wa
    #
    @16
    @18
    wph
    @16
    @25
    @18
    wph
    @16
    @25
    wa
    #
    @18
    wph
    @27
    @18
    wph
    @27
    wps
    @25
    wa
    #
    wps
    pm3.24
    #
    wph
    @16
    wps
    @25
    wph
    cY
    cV
    wcel
    #
    @16
    wps
    wb
    ifeqeqx.y
    wch
    wps
    vx
    cY
    cV
    ifeqeqx.4
    sbcieg
    syl
    anbi1d
    mtbiri
    pm2.21d
    imp
    anass1rs
    ex
    ifbothda
    sylc
    @5
    @1
    @9
    @5
    cA
    @8
    @0
    vx
    @4
    cA
    csbeq1a
    eqeq2d
    biimprd
    sylc
    @6
    wch
    wn
    #
    wa
    #
    @5
    @0
    vx
    @4
    cB
    csb
    #
    wceq
    #
    @2
    wph
    @5
    @31
    simplr
    #
    @32
    wph
    @11
    wn
    #
    @34
    wph
    @5
    @31
    simpll
    @32
    @5
    @31
    @36
    @35
    @6
    @31
    simpr
    @5
    @31
    @36
    @5
    wch
    @11
    @12
    notbid
    biimpd
    sylc
    wps
    @13
    wn
    #
    @0
    vx
    cX
    cB
    csb
    #
    wceq
    #
    wi
    @16
    wn
    #
    @0
    vx
    cY
    cB
    csb
    #
    wceq
    #
    wi
    @36
    @34
    wi
    wph
    cX
    cY
    @19
    @37
    @36
    @39
    @34
    @19
    @13
    @11
    @20
    notbid
    @19
    @38
    @33
    @0
    vx
    cX
    @4
    cB
    csbeq1
    eqeq2d
    imbi12d
    @21
    @40
    @36
    @42
    @34
    @21
    @16
    @11
    @22
    notbid
    @21
    @41
    @33
    @0
    vx
    cY
    @4
    cB
    csbeq1
    eqeq2d
    imbi12d
    wph
    wps
    @37
    @39
    wph
    wps
    @37
    wa
    #
    @39
    wph
    @43
    @28
    @29
    wph
    @37
    @25
    wps
    wph
    @37
    wth
    wps
    wph
    @37
    wth
    wn
    wph
    @13
    wth
    wph
    @24
    @13
    wth
    wb
    ifeqeqx.x
    wch
    wth
    vx
    cX
    cW
    ifeqeqx.3
    sbcieg
    syl
    notbid
    biimpd
    wph
    wps
    wth
    ifeqeqx.6
    ex
    nsyld
    anim2d
    mtoi
    pm2.21d
    expdimp
    @26
    @42
    @40
    @26
    @41
    @0
    wph
    @41
    @0
    wceq
    #
    @25
    wph
    @30
    @44
    ifeqeqx.y
    vx
    cY
    cB
    @0
    cV
    @30
    vx
    @0
    nfcvd
    ifeqeqx.2
    csbiegf
    syl
    adantr
    eqcomd
    a1d
    ifbothda
    sylc
    @5
    @2
    @34
    @5
    cB
    @33
    @0
    vx
    @4
    cB
    csbeq1a
    eqeq2d
    biimprd
    sylc
    ifbothda
end
