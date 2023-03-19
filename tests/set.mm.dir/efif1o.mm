include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "cres.mm"
include "cmul.mm"
include "caddc.mm"
include "cioc.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "readdcl.mm"
include "mpan2.mm"
include "elioc2.mm"
include "syl2anc.mm"
include "simp1.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "syl5eqss.mm"
include "efif1olem1.mm"
include "efif1olem2.mm"
include "eqid.mm"
include "efif1olem4.mm"

theorem efif1o
  let vw: setvar w
  let cA: class A
  let cC: class C
  let cD: class D
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cS: class S
  assume efif1o.1: |- F = ( w e. D |-> ( exp ` ( _i x. w ) ) )
  assume efif1o.2: |- C = ( `' abs " { 1 } )
  assume efif1o.3: |- D = ( A (,] ( A + ( 2 x. _pi ) ) )

  disjoint A w
  disjoint C w
  disjoint D w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( A e. RR -> F : D -1-1-onto-> C )

  proof
    cA
    cr
    wcel
    #
    vx
    vy
    vz
    vw
    cC
    cD
    csin
    cpi
    c2
    cdiv
    co
    #
    cneg
    @1
    cicc
    co
    cres
    #
    cF
    efif1o.1
    efif1o.2
    @0
    cD
    cA
    cA
    c2
    cpi
    cmul
    co
    #
    caddc
    co
    #
    cioc
    co
    #
    cr
    efif1o.3
    @0
    vx
    @5
    cr
    @0
    vx
    cv
    #
    @5
    wcel
    #
    @6
    cr
    wcel
    #
    cA
    @6
    clt
    wbr
    #
    @6
    @4
    cle
    wbr
    #
    w3a
    #
    @8
    @0
    cA
    cxr
    wcel
    @4
    cr
    wcel
    #
    @7
    @11
    wb
    cA
    rexr
    @0
    @3
    cr
    wcel
    @12
    c2
    cpi
    2re
    pire
    remulcli
    cA
    @3
    readdcl
    mpan2
    cA
    @4
    @6
    elioc2
    syl2anc
    @8
    @9
    @10
    simp1
    syl6bi
    ssrdv
    syl5eqss
    vx
    vy
    cA
    cD
    efif1o.3
    efif1olem1
    vy
    vz
    cA
    cD
    efif1o.3
    efif1olem2
    @2
    eqid
    efif1olem4
end
