include "wss.mm"
include "ssid.mm"
include "wi.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "wcel.mm"
include "wal.mm"
include "con0.mm"
include "cv.mm"
include "weq.mm"
include "eqeq2.mm"
include "sseq1.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "albidv.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "cbvalv.mm"
include "syl6bb.mm"
include "wral.mm"
include "w3a.mm"
include "simp3l.mm"
include "simp2.mm"
include "simp1l.mm"
include "eqeltrd.mm"
include "simp3r.mm"
include "eqsstrd.mm"
include "csb.mm"
include "wsb.mm"
include "simpl3l.mm"
include "simpl1l.mm"
include "simpr.mm"
include "simpl2.mm"
include "eleqtrd.mm"
include "onelss.mm"
include "sylc.mm"
include "simpl3r.mm"
include "sstrd.mm"
include "simpl1r.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "nfcv.mm"
include "csbhypf.mm"
include "eqcomd.mm"
include "equcoms.mm"
include "wb.mm"
include "nfv.mm"
include "sbhypf.mm"
include "bicomd.mm"
include "spv.mm"
include "mp2and.mm"
include "ex.mm"
include "alrimiv.mm"
include "eleq1d.mm"
include "sylib.mm"
include "syl121anc.mm"
include "3exp.mm"
include "tfis3.mm"
include "syl.mm"
include "spcgv.mm"
include "mpi.mm"
include "expd.mm"
include "pm2.43i.mm"

theorem tfisi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume tfisi.a: |- ( ph -> A e. V )
  assume tfisi.b: |- ( ph -> T e. On )
  assume tfisi.c: |- ( ( ph /\ ( R e. On /\ R C_ T ) /\ A. y ( S e. R -> ch ) ) -> ps )
  assume tfisi.d: |- ( x = y -> ( ps <-> ch ) )
  assume tfisi.e: |- ( x = A -> ( ps <-> th ) )
  assume tfisi.f: |- ( x = y -> R = S )
  assume tfisi.g: |- ( x = A -> R = T )

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint R y
  disjoint S x
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint A x
  disjoint th x
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint y z
  disjoint T z
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint ch v
  disjoint ch w
  disjoint ch z
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint ps w
  disjoint ps z
  assert |- ( ph -> th )

  proof
    wph
    cT
    cT
    wss
    #
    wth
    cT
    ssid
    wph
    @0
    wth
    wi
    wph
    wph
    @0
    wth
    wph
    cT
    cT
    wceq
    #
    wph
    @0
    wa
    #
    wth
    wi
    #
    cT
    eqid
    wph
    cA
    cV
    wcel
    cR
    cT
    wceq
    #
    @2
    wps
    wi
    #
    wi
    #
    vx
    wal
    #
    @1
    @3
    wi
    #
    tfisi.a
    wph
    cT
    con0
    wcel
    @7
    tfisi.b
    cR
    vz
    cv
    #
    wceq
    #
    wph
    @9
    cT
    wss
    #
    wa
    #
    wps
    wi
    #
    wi
    #
    vx
    wal
    #
    cS
    vw
    cv
    #
    wceq
    #
    wph
    @16
    cT
    wss
    #
    wa
    #
    wch
    wi
    #
    wi
    #
    vy
    wal
    #
    @7
    vz
    vw
    cT
    vz
    vw
    weq
    #
    @15
    cR
    @16
    wceq
    #
    @19
    wps
    wi
    #
    wi
    #
    vx
    wal
    @22
    @23
    @14
    @26
    vx
    @23
    @10
    @24
    @13
    @25
    @9
    @16
    cR
    eqeq2
    @23
    @12
    @19
    wps
    @23
    @11
    @18
    wph
    @9
    @16
    cT
    sseq1
    anbi2d
    imbi1d
    imbi12d
    albidv
    @26
    @21
    vx
    vy
    vx
    vy
    weq
    #
    @24
    @17
    @25
    @20
    @27
    cR
    cS
    @16
    tfisi.f
    eqeq1d
    @27
    wps
    wch
    @19
    tfisi.d
    imbi2d
    imbi12d
    cbvalv
    syl6bb
    @9
    cT
    wceq
    #
    @14
    @6
    vx
    @28
    @10
    @4
    @13
    @5
    @9
    cT
    cR
    eqeq2
    @28
    @12
    @2
    wps
    @28
    @11
    @0
    wph
    @9
    cT
    cT
    sseq1
    anbi2d
    imbi1d
    imbi12d
    albidv
    @9
    con0
    wcel
    #
    @22
    vw
    @9
    wral
    #
    @15
    @29
    @30
    wa
    #
    @14
    vx
    @31
    @10
    @12
    wps
    @31
    @10
    @12
    w3a
    #
    wph
    cR
    con0
    wcel
    cR
    cT
    wss
    cS
    cR
    wcel
    #
    wch
    wi
    #
    vy
    wal
    #
    wps
    @31
    @10
    wph
    @11
    simp3l
    @32
    cR
    @9
    con0
    @31
    @10
    @12
    simp2
    #
    @29
    @30
    @10
    @12
    simp1l
    eqeltrd
    @32
    cR
    @9
    cT
    @36
    @31
    @10
    wph
    @11
    simp3r
    eqsstrd
    @32
    vx
    vv
    cv
    cR
    csb
    #
    cR
    wcel
    #
    wps
    vx
    vv
    wsb
    #
    wi
    #
    vv
    wal
    @35
    @32
    @40
    vv
    @32
    @38
    @39
    @32
    @38
    wa
    #
    wph
    @37
    cT
    wss
    #
    @39
    wph
    @11
    @31
    @10
    @38
    simpl3l
    @41
    @37
    @9
    cT
    @41
    @29
    @37
    @9
    wcel
    #
    @37
    @9
    wss
    @29
    @30
    @10
    @12
    @38
    simpl1l
    @41
    @37
    cR
    @9
    @32
    @38
    simpr
    @31
    @10
    @12
    @38
    simpl2
    eleqtrd
    #
    @9
    @37
    onelss
    sylc
    wph
    @11
    @31
    @10
    @38
    simpl3r
    sstrd
    @41
    cS
    @37
    wceq
    #
    wph
    @42
    wa
    #
    wch
    wi
    #
    wi
    #
    vy
    wal
    #
    @37
    @37
    wceq
    #
    @46
    @39
    wi
    #
    @41
    @43
    @30
    @49
    @44
    @29
    @30
    @10
    @12
    @38
    simpl1r
    @22
    @49
    vw
    @37
    @9
    @16
    @37
    wceq
    #
    @21
    @48
    vy
    @52
    @17
    @45
    @20
    @47
    @16
    @37
    cS
    eqeq2
    @52
    @19
    @46
    wch
    @52
    @18
    @42
    wph
    @16
    @37
    cT
    sseq1
    anbi2d
    imbi1d
    imbi12d
    albidv
    rspcva
    syl2anc
    @41
    @37
    eqidd
    @48
    @50
    @51
    wi
    vy
    vv
    vy
    vv
    weq
    #
    @45
    @50
    @47
    @51
    @53
    cS
    @37
    @37
    @45
    vv
    vy
    vv
    vy
    weq
    #
    @37
    cS
    vx
    vv
    vy
    cv
    #
    cR
    cS
    vx
    @55
    nfcv
    vx
    cS
    nfcv
    tfisi.f
    csbhypf
    #
    eqcomd
    equcoms
    eqeq1d
    @53
    wch
    @39
    @46
    wch
    @39
    wb
    vv
    vy
    @54
    @39
    wch
    wps
    wch
    vx
    vv
    @55
    wch
    vx
    nfv
    tfisi.d
    sbhypf
    #
    bicomd
    equcoms
    imbi2d
    imbi12d
    spv
    sylc
    mp2and
    ex
    alrimiv
    @40
    @34
    vv
    vy
    @54
    @38
    @33
    @39
    wch
    @54
    @37
    cS
    cR
    @56
    eleq1d
    @57
    imbi12d
    cbvalv
    sylib
    tfisi.c
    syl121anc
    3exp
    alrimiv
    ex
    tfis3
    syl
    @6
    @8
    vx
    cA
    cV
    vx
    cv
    cA
    wceq
    #
    @4
    @1
    @5
    @3
    @58
    cR
    cT
    cT
    tfisi.g
    eqeq1d
    @58
    wps
    wth
    @2
    tfisi.e
    imbi2d
    imbi12d
    spcgv
    sylc
    mpi
    expd
    pm2.43i
    mpi
end
