include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "cc.mm"
include "cr.mm"
include "wf.mm"
include "ref.mm"
include "fco.mm"
include "sylancr.mm"
include "cres.mm"
include "resco.mm"
include "wa.mm"
include "cin.mm"
include "wb.mm"
include "fresin.mm"
include "ismbfcn.mm"
include "3syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "syl5eqel.mm"
include "mbfres2.mm"
include "imf.mm"
include "simprd.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem mbfres2cn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume mbfres2cn.f: |- ( ph -> F : A --> CC )
  assume mbfres2cn.b: |- ( ph -> ( F |` B ) e. MblFn )
  assume mbfres2cn.c: |- ( ph -> ( F |` C ) e. MblFn )
  assume mbfres2cn.a: |- ( ph -> ( B u. C ) = A )


  assert |- ( ph -> F e. MblFn )

  proof
    wph
    cF
    cmbf
    wcel
    #
    cre
    cF
    ccom
    #
    cmbf
    wcel
    #
    cim
    cF
    ccom
    #
    cmbf
    wcel
    #
    wph
    cA
    cB
    cC
    @1
    wph
    cc
    cr
    cre
    wf
    cA
    cc
    cF
    wf
    #
    cA
    cr
    @1
    wf
    ref
    mbfres2cn.f
    cA
    cc
    cr
    cre
    cF
    fco
    sylancr
    wph
    @1
    cB
    cres
    cre
    cF
    cB
    cres
    #
    ccom
    #
    cmbf
    cre
    cF
    cB
    resco
    wph
    @7
    cmbf
    wcel
    #
    cim
    @6
    ccom
    #
    cmbf
    wcel
    #
    wph
    @6
    cmbf
    wcel
    #
    @8
    @10
    wa
    #
    mbfres2cn.b
    wph
    @5
    cA
    cB
    cin
    #
    cc
    @6
    wf
    @11
    @12
    wb
    mbfres2cn.f
    cA
    cc
    cF
    cB
    fresin
    @13
    @6
    ismbfcn
    3syl
    mpbid
    #
    simpld
    syl5eqel
    wph
    @1
    cC
    cres
    cre
    cF
    cC
    cres
    #
    ccom
    #
    cmbf
    cre
    cF
    cC
    resco
    wph
    @16
    cmbf
    wcel
    #
    cim
    @15
    ccom
    #
    cmbf
    wcel
    #
    wph
    @15
    cmbf
    wcel
    #
    @17
    @19
    wa
    #
    mbfres2cn.c
    wph
    @5
    cA
    cC
    cin
    #
    cc
    @15
    wf
    @20
    @21
    wb
    mbfres2cn.f
    cA
    cc
    cF
    cC
    fresin
    @22
    @15
    ismbfcn
    3syl
    mpbid
    #
    simpld
    syl5eqel
    mbfres2cn.a
    mbfres2
    wph
    cA
    cB
    cC
    @3
    wph
    cc
    cr
    cim
    wf
    @5
    cA
    cr
    @3
    wf
    imf
    mbfres2cn.f
    cA
    cc
    cr
    cim
    cF
    fco
    sylancr
    wph
    @3
    cB
    cres
    @9
    cmbf
    cim
    cF
    cB
    resco
    wph
    @8
    @10
    @14
    simprd
    syl5eqel
    wph
    @3
    cC
    cres
    @18
    cmbf
    cim
    cF
    cC
    resco
    wph
    @17
    @19
    @23
    simprd
    syl5eqel
    mbfres2cn.a
    mbfres2
    wph
    @5
    @0
    @2
    @4
    wa
    wb
    mbfres2cn.f
    cA
    cF
    ismbfcn
    syl
    mpbir2and
end
