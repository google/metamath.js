include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "cv.mm"
include "wiso.mm"
include "cab.mm"
include "wcel.mm"
include "cio.mm"
include "weu.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cr.mm"
include "wss.mm"
include "wor.mm"
include "ltso.mm"
include "soss.mm"
include "mpisyl.mm"
include "0zd.mm"
include "eqid.mm"
include "fzisoeu.mm"
include "wceq.mm"
include "wb.mm"
include "cneg.mm"
include "cfn.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "negsubd.mm"
include "df-neg.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "oveq2d.mm"
include "isoeq4.mm"
include "eubidv.mm"
include "mpbid.mm"
include "iotacl.mm"
include "syl5eqel.mm"
include "cvv.mm"
include "iotaex.mm"
include "eqeltri.mm"
include "isoeq1.mm"
include "elab.mm"
include "sylib.mm"

theorem fourierdlem36
  let wph: wff ph
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem36.a: |- ( ph -> A e. Fin )
  assume fourierdlem36.assr: |- ( ph -> A C_ RR )
  assume fourierdlem36.f: |- F = ( iota f f Isom < , < ( ( 0 ... N ) , A ) )
  assume fourierdlem36.n: |- N = ( ( # ` A ) - 1 )

  disjoint A f
  disjoint F f
  disjoint N f
  disjoint f ph
  disjoint k x
  assert |- ( ph -> F Isom < , < ( ( 0 ... N ) , A ) )

  proof
    wph
    cF
    cc0
    cN
    cfz
    co
    #
    cA
    clt
    clt
    vf
    cv
    #
    wiso
    #
    vf
    cab
    #
    wcel
    @0
    cA
    clt
    clt
    cF
    wiso
    #
    wph
    cF
    @2
    vf
    cio
    #
    @3
    fourierdlem36.f
    wph
    @2
    vf
    weu
    #
    @5
    @3
    wcel
    wph
    cc0
    cA
    chash
    cfv
    #
    cc0
    c1
    cmin
    co
    #
    caddc
    co
    #
    cfz
    co
    #
    cA
    clt
    clt
    @1
    wiso
    #
    vf
    weu
    @6
    wph
    vf
    cA
    cc0
    @9
    fourierdlem36.a
    wph
    cA
    cr
    wss
    cr
    clt
    wor
    cA
    clt
    wor
    fourierdlem36.assr
    ltso
    cA
    cr
    clt
    soss
    mpisyl
    wph
    0zd
    @9
    eqid
    fzisoeu
    wph
    @11
    @2
    vf
    wph
    @10
    @0
    wceq
    @11
    @2
    wb
    wph
    @9
    cN
    cc0
    cfz
    wph
    @7
    c1
    cneg
    #
    caddc
    co
    @7
    c1
    cmin
    co
    @9
    cN
    wph
    @7
    c1
    wph
    @7
    wph
    cA
    cfn
    wcel
    @7
    cn0
    wcel
    fourierdlem36.a
    cA
    hashcl
    syl
    nn0cnd
    wph
    1cnd
    negsubd
    @8
    @12
    @7
    caddc
    @12
    @8
    c1
    df-neg
    eqcomi
    oveq2i
    fourierdlem36.n
    3eqtr4g
    oveq2d
    @10
    cA
    @0
    clt
    clt
    @1
    isoeq4
    syl
    eubidv
    mpbid
    @2
    vf
    iotacl
    syl
    syl5eqel
    @2
    @4
    vf
    cF
    cF
    @5
    cvv
    fourierdlem36.f
    @2
    vf
    iotaex
    eqeltri
    @0
    cA
    clt
    clt
    cF
    @1
    isoeq1
    elab
    sylib
end
