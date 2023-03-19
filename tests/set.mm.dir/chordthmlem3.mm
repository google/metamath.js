include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "cdiv.mm"
include "addcld.mm"
include "halfcld.mm"
include "eqeltrd.mm"
include "subcld.mm"
include "abscld.mm"
include "recnd.mm"
include "sqcld.mm"
include "adantr.mm"
include "addid1d.mm"
include "cmul.mm"
include "c1.mm"
include "mulcld.mm"
include "1cnd.mm"
include "simpr.mm"
include "subeq0bd.mm"
include "abs00bd.mm"
include "sq0id.mm"
include "oveq2d.mm"
include "abssubd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "3eqtr4rd.mm"
include "addid2d.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "clog.mm"
include "cim.mm"
include "cmpt2.mm"
include "cpi.mm"
include "cneg.mm"
include "cpr.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "cr.mm"
include "chordthmlem2.mm"
include "pythag.mm"
include "syl321anc.mm"
include "pm2.61da2ne.mm"

theorem chordthmlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume chordthmlem3.A: |- ( ph -> A e. CC )
  assume chordthmlem3.B: |- ( ph -> B e. CC )
  assume chordthmlem3.Q: |- ( ph -> Q e. CC )
  assume chordthmlem3.X: |- ( ph -> X e. RR )
  assume chordthmlem3.M: |- ( ph -> M = ( ( A + B ) / 2 ) )
  assume chordthmlem3.P: |- ( ph -> P = ( ( X x. A ) + ( ( 1 - X ) x. B ) ) )
  assume chordthmlem3.ABequidistQ: |- ( ph -> ( abs ` ( A - Q ) ) = ( abs ` ( B - Q ) ) )


  assert |- ( ph -> ( ( abs ` ( P - Q ) ) ^ 2 ) = ( ( ( abs ` ( Q - M ) ) ^ 2 ) + ( ( abs ` ( P - M ) ) ^ 2 ) ) )

  proof
    wph
    cP
    cQ
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cQ
    cM
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cP
    cM
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    cP
    cM
    cQ
    cM
    wph
    cP
    cM
    wceq
    #
    wa
    #
    @5
    cc0
    caddc
    co
    @5
    @9
    @2
    @12
    @5
    wph
    @5
    cc
    wcel
    @11
    wph
    @4
    wph
    @4
    wph
    @3
    wph
    cQ
    cM
    chordthmlem3.Q
    wph
    cM
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cc
    chordthmlem3.M
    wph
    @13
    wph
    cA
    cB
    chordthmlem3.A
    chordthmlem3.B
    addcld
    halfcld
    eqeltrd
    #
    subcld
    abscld
    recnd
    sqcld
    adantr
    addid1d
    @12
    @8
    cc0
    @5
    caddc
    @12
    @7
    @12
    @6
    @12
    cP
    cM
    wph
    cP
    cc
    wcel
    #
    @11
    wph
    cP
    cX
    cA
    cmul
    co
    #
    c1
    cX
    cmin
    co
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    cc
    chordthmlem3.P
    wph
    @17
    @19
    wph
    cX
    cA
    wph
    cX
    chordthmlem3.X
    recnd
    #
    chordthmlem3.A
    mulcld
    wph
    @18
    cB
    wph
    c1
    cX
    wph
    1cnd
    @21
    subcld
    chordthmlem3.B
    mulcld
    addcld
    eqeltrd
    #
    adantr
    #
    wph
    @11
    simpr
    #
    subeq0bd
    abs00bd
    sq0id
    oveq2d
    @12
    @1
    @4
    c2
    cexp
    @12
    cQ
    cP
    cmin
    co
    #
    cabs
    cfv
    @1
    @4
    @12
    cQ
    cP
    wph
    cQ
    cc
    wcel
    #
    @11
    chordthmlem3.Q
    adantr
    @23
    abssubd
    @12
    @25
    @3
    cabs
    @12
    cP
    cM
    cQ
    cmin
    @24
    oveq2d
    fveq2d
    eqtr3d
    oveq1d
    3eqtr4rd
    wph
    cQ
    cM
    wceq
    #
    wa
    #
    cc0
    @8
    caddc
    co
    @8
    @9
    @2
    @28
    @8
    wph
    @8
    cc
    wcel
    @27
    wph
    @7
    wph
    @7
    wph
    @6
    wph
    cP
    cM
    @22
    @15
    subcld
    abscld
    recnd
    sqcld
    adantr
    addid2d
    @28
    @5
    cc0
    @8
    caddc
    @28
    @4
    @28
    @3
    @28
    cQ
    cM
    wph
    @26
    @27
    chordthmlem3.Q
    adantr
    wph
    @27
    simpr
    #
    subeq0bd
    abs00bd
    sq0id
    oveq1d
    @28
    @1
    @7
    c2
    cexp
    @28
    @0
    @6
    cabs
    @28
    cQ
    cM
    cP
    cmin
    @29
    oveq2d
    fveq2d
    oveq1d
    3eqtr4rd
    wph
    cP
    cM
    wne
    #
    cQ
    cM
    wne
    #
    wa
    #
    wa
    #
    @16
    @26
    cM
    cc
    wcel
    #
    @30
    @31
    @3
    @6
    vx
    vy
    cc
    cc0
    csn
    cdif
    #
    @35
    vy
    cv
    vx
    cv
    cdiv
    co
    clog
    cfv
    cim
    cfv
    cmpt2
    #
    co
    #
    cpi
    c2
    cdiv
    co
    #
    @38
    cneg
    cpr
    wcel
    @10
    wph
    @16
    @32
    @22
    adantr
    wph
    @26
    @32
    chordthmlem3.Q
    adantr
    #
    wph
    @34
    @32
    @15
    adantr
    wph
    @30
    @31
    simprl
    #
    wph
    @30
    @31
    simprr
    #
    @33
    vx
    vy
    cA
    cB
    cP
    cQ
    @36
    cM
    cX
    @36
    eqid
    #
    wph
    cA
    cc
    wcel
    @32
    chordthmlem3.A
    adantr
    wph
    cB
    cc
    wcel
    @32
    chordthmlem3.B
    adantr
    @39
    wph
    cX
    cr
    wcel
    @32
    chordthmlem3.X
    adantr
    wph
    cM
    @14
    wceq
    @32
    chordthmlem3.M
    adantr
    wph
    cP
    @20
    wceq
    @32
    chordthmlem3.P
    adantr
    wph
    cA
    cQ
    cmin
    co
    cabs
    cfv
    cB
    cQ
    cmin
    co
    cabs
    cfv
    wceq
    @32
    chordthmlem3.ABequidistQ
    adantr
    @40
    @41
    chordthmlem2
    vx
    vy
    cP
    cQ
    cM
    @36
    @37
    @4
    @7
    @1
    @42
    @4
    eqid
    @7
    eqid
    @1
    eqid
    @37
    eqid
    pythag
    syl321anc
    pm2.61da2ne
end
