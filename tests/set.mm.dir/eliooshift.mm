include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cioo.mm"
include "readdcld.mm"
include "2thd.mm"
include "ltadd1d.mm"
include "bicomd.mm"
include "3anbi123d.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "elioo2.mm"
include "syl2anc.mm"
include "3bitr4rd.mm"

theorem eliooshift
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume eliooshift.a: |- ( ph -> A e. RR )
  assume eliooshift.b: |- ( ph -> B e. RR )
  assume eliooshift.c: |- ( ph -> C e. RR )
  assume eliooshift.d: |- ( ph -> D e. RR )


  assert |- ( ph -> ( A e. ( B (,) C ) <-> ( A + D ) e. ( ( B + D ) (,) ( C + D ) ) ) )

  proof
    wph
    cA
    cD
    caddc
    co
    #
    cr
    wcel
    #
    cB
    cD
    caddc
    co
    #
    @0
    clt
    wbr
    #
    @0
    cC
    cD
    caddc
    co
    #
    clt
    wbr
    #
    w3a
    #
    cA
    cr
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    w3a
    #
    @0
    @2
    @4
    cioo
    co
    wcel
    #
    cA
    cB
    cC
    cioo
    co
    wcel
    #
    wph
    @1
    @7
    @3
    @8
    @5
    @9
    wph
    @1
    @7
    wph
    cA
    cD
    eliooshift.a
    eliooshift.d
    readdcld
    eliooshift.a
    2thd
    wph
    @8
    @3
    wph
    cB
    cA
    cD
    eliooshift.b
    eliooshift.a
    eliooshift.d
    ltadd1d
    bicomd
    wph
    @9
    @5
    wph
    cA
    cC
    cD
    eliooshift.a
    eliooshift.c
    eliooshift.d
    ltadd1d
    bicomd
    3anbi123d
    wph
    @2
    cxr
    wcel
    @4
    cxr
    wcel
    @11
    @6
    wb
    wph
    @2
    wph
    cB
    cD
    eliooshift.b
    eliooshift.d
    readdcld
    rexrd
    wph
    @4
    wph
    cC
    cD
    eliooshift.c
    eliooshift.d
    readdcld
    rexrd
    @2
    @4
    @0
    elioo2
    syl2anc
    wph
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    @12
    @10
    wb
    wph
    cB
    eliooshift.b
    rexrd
    wph
    cC
    eliooshift.c
    rexrd
    cB
    cC
    cA
    elioo2
    syl2anc
    3bitr4rd
end
