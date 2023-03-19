include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cmul.mm"
include "c2.mm"
include "cfz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "elfznn.mm"
include "syl.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "nn0nnaddcl.mm"
include "syl2anc.mm"
include "nnmulcld.mm"
include "nnaddcld.mm"
include "nnred.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "sylancr.mm"
include "elfzle2.mm"
include "wb.mm"
include "cr.mm"
include "nnre.mm"
include "leadd1.mm"
include "syl3an.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "nncnd.mm"
include "1cnd.mm"
include "adddid.mm"
include "nn0cnd.mm"
include "addassd.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "pncan3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"
include "leadd1dd.mm"
include "2timesd.mm"
include "cc0.mm"
include "clt.mm"
include "nngt0d.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "letrd.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnzd.mm"
include "elfz5.mm"
include "mpbird.mm"

theorem vdwlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cK: class K
  let cJ: class J
  let cP: class P
  let cR: class R
  let cH: class H
  let cM: class M
  let cD: class D
  let cE: class E
  let cT: class T
  assume vdwlem3.v: |- ( ph -> V e. NN )
  assume vdwlem3.w: |- ( ph -> W e. NN )
  assume vdwlem3.a: |- ( ph -> A e. ( 1 ... V ) )
  assume vdwlem3.b: |- ( ph -> B e. ( 1 ... W ) )


  assert |- ( ph -> ( B + ( W x. ( ( A - 1 ) + V ) ) ) e. ( 1 ... ( W x. ( 2 x. V ) ) ) )

  proof
    wph
    cB
    cW
    cA
    c1
    cmin
    co
    #
    cV
    caddc
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c1
    cW
    c2
    cV
    cmul
    co
    #
    cmul
    co
    #
    cfz
    co
    wcel
    #
    @3
    @5
    cle
    wbr
    #
    wph
    @3
    cW
    cA
    cV
    caddc
    co
    #
    cmul
    co
    #
    @5
    wph
    @3
    wph
    cB
    @2
    wph
    cB
    c1
    cW
    cfz
    co
    wcel
    #
    cB
    cn
    wcel
    #
    vdwlem3.b
    cB
    cW
    elfznn
    syl
    #
    wph
    cW
    @1
    vdwlem3.w
    wph
    @0
    cn0
    wcel
    #
    cV
    cn
    wcel
    #
    @1
    cn
    wcel
    wph
    cA
    cn
    wcel
    #
    @13
    wph
    cA
    c1
    cV
    cfz
    co
    wcel
    #
    @15
    vdwlem3.a
    cA
    cV
    elfznn
    syl
    #
    cA
    nnm1nn0
    syl
    #
    vdwlem3.v
    @0
    cV
    nn0nnaddcl
    syl2anc
    #
    nnmulcld
    #
    nnaddcld
    #
    nnred
    wph
    @9
    wph
    cW
    @8
    vdwlem3.w
    wph
    cA
    cV
    @17
    vdwlem3.v
    nnaddcld
    #
    nnmulcld
    nnred
    wph
    @5
    wph
    cW
    @4
    vdwlem3.w
    wph
    c2
    cn
    wcel
    @14
    @4
    cn
    wcel
    2nn
    vdwlem3.v
    c2
    cV
    nnmulcl
    sylancr
    #
    nnmulcld
    #
    nnred
    wph
    @3
    cW
    @2
    caddc
    co
    #
    @9
    cle
    wph
    cB
    cW
    cle
    wbr
    #
    @3
    @25
    cle
    wbr
    #
    wph
    @10
    @26
    vdwlem3.b
    cB
    c1
    cW
    elfzle2
    syl
    wph
    @11
    cW
    cn
    wcel
    #
    @2
    cn
    wcel
    #
    @26
    @27
    wb
    #
    @12
    vdwlem3.w
    @20
    @11
    cB
    cr
    wcel
    @28
    cW
    cr
    wcel
    #
    @29
    @2
    cr
    wcel
    @30
    cB
    nnre
    cW
    nnre
    @2
    nnre
    cB
    cW
    @2
    leadd1
    syl3an
    syl3anc
    mpbid
    wph
    cW
    c1
    @1
    caddc
    co
    #
    cmul
    co
    cW
    c1
    cmul
    co
    #
    @2
    caddc
    co
    @9
    @25
    wph
    cW
    c1
    @1
    wph
    cW
    vdwlem3.w
    nncnd
    #
    wph
    1cnd
    #
    wph
    @1
    @19
    nncnd
    adddid
    wph
    @32
    @8
    cW
    cmul
    wph
    c1
    @0
    caddc
    co
    #
    cV
    caddc
    co
    @32
    @8
    wph
    c1
    @0
    cV
    @35
    wph
    @0
    @18
    nn0cnd
    wph
    cV
    vdwlem3.v
    nncnd
    #
    addassd
    wph
    @36
    cA
    cV
    caddc
    wph
    c1
    cc
    wcel
    cA
    cc
    wcel
    @36
    cA
    wceq
    ax-1cn
    wph
    cA
    @17
    nncnd
    c1
    cA
    pncan3
    sylancr
    oveq1d
    eqtr3d
    oveq2d
    wph
    @33
    cW
    @2
    caddc
    wph
    cW
    @34
    mulid1d
    oveq1d
    3eqtr3d
    breqtrrd
    wph
    @8
    @4
    cle
    wbr
    #
    @9
    @5
    cle
    wbr
    #
    wph
    @8
    cV
    cV
    caddc
    co
    @4
    cle
    wph
    cA
    cV
    cV
    wph
    cA
    @17
    nnred
    wph
    cV
    vdwlem3.v
    nnred
    #
    @40
    wph
    @16
    cA
    cV
    cle
    wbr
    vdwlem3.a
    cA
    c1
    cV
    elfzle2
    syl
    leadd1dd
    wph
    cV
    @37
    2timesd
    breqtrrd
    wph
    @8
    cr
    wcel
    @4
    cr
    wcel
    @31
    cc0
    cW
    clt
    wbr
    @38
    @39
    wb
    wph
    @8
    @22
    nnred
    wph
    @4
    @23
    nnred
    wph
    cW
    vdwlem3.w
    nnred
    wph
    cW
    vdwlem3.w
    nngt0d
    @8
    @4
    cW
    lemul2
    syl112anc
    mpbid
    letrd
    wph
    @3
    c1
    cuz
    cfv
    #
    wcel
    @5
    cz
    wcel
    @6
    @7
    wb
    wph
    @3
    cn
    @41
    @21
    nnuz
    syl6eleq
    wph
    @5
    @24
    nnzd
    @3
    c1
    @5
    elfz5
    syl2anc
    mpbird
end
