include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cabs.mm"
include "cif.mm"
include "simpr.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "cc.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "syl.mm"
include "imcld.mm"
include "adantr.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "wb.mm"
include "reim0b.mm"
include "simprbi.mm"
include "sylbird.mm"
include "necon3bd.mm"
include "imp.mm"
include "absrpcld.mm"
include "ifclda.mm"
include "syl5eqel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "logdmn0.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "sylancr.mm"
include "rpdivcld.mm"
include "rpmulcld.mm"
include "ifcld.mm"

theorem logcnlem2
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume logcnlem.s: |- S = if ( A e. RR+ , A , ( abs ` ( Im ` A ) ) )
  assume logcnlem.t: |- T = ( ( abs ` A ) x. ( R / ( 1 + R ) ) )
  assume logcnlem.a: |- ( ph -> A e. D )
  assume logcnlem.r: |- ( ph -> R e. RR+ )


  assert |- ( ph -> if ( S <_ T , S , T ) e. RR+ )

  proof
    wph
    cS
    cT
    cle
    wbr
    cS
    cT
    crp
    wph
    cS
    cA
    crp
    wcel
    #
    cA
    cA
    cim
    cfv
    #
    cabs
    cfv
    #
    cif
    crp
    logcnlem.s
    wph
    @0
    cA
    @2
    crp
    wph
    @0
    simpr
    wph
    @0
    wn
    #
    wa
    #
    @1
    @4
    @1
    wph
    @1
    cr
    wcel
    @3
    wph
    cA
    wph
    cA
    cD
    wcel
    #
    cA
    cc
    wcel
    #
    logcnlem.a
    @5
    @6
    cA
    cr
    wcel
    #
    @0
    wi
    #
    cA
    cD
    logcn.d
    ellogdm
    #
    simplbi
    syl
    #
    imcld
    adantr
    recnd
    wph
    @3
    @1
    cc0
    wne
    wph
    @0
    @1
    cc0
    wph
    @1
    cc0
    wceq
    #
    @7
    @0
    wph
    @6
    @7
    @11
    wb
    @10
    cA
    reim0b
    syl
    wph
    @5
    @8
    logcnlem.a
    @5
    @6
    @8
    @9
    simprbi
    syl
    sylbird
    necon3bd
    imp
    absrpcld
    ifclda
    syl5eqel
    wph
    cT
    cA
    cabs
    cfv
    #
    cR
    c1
    cR
    caddc
    co
    #
    cdiv
    co
    #
    cmul
    co
    crp
    logcnlem.t
    wph
    @12
    @14
    wph
    cA
    @10
    wph
    @5
    cA
    cc0
    wne
    logcnlem.a
    cA
    cD
    logcn.d
    logdmn0
    syl
    absrpcld
    wph
    cR
    @13
    logcnlem.r
    wph
    c1
    crp
    wcel
    cR
    crp
    wcel
    @13
    crp
    wcel
    1rp
    logcnlem.r
    c1
    cR
    rpaddcl
    sylancr
    rpdivcld
    rpmulcld
    syl5eqel
    ifcld
end
