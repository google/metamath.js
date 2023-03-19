include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "clt.mm"
include "cxr.mm"
include "cc0.mm"
include "cfz.mm"
include "cmap.mm"
include "wcel.mm"
include "wbr.mm"
include "cn.mm"
include "ciccp.mm"
include "cfzo.mm"
include "wa.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "fzval3.mm"
include "eleq2d.mm"
include "syl.mm"
include "mpbid.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "pncan1.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "elfzelz.mm"
include "peano2zd.mm"
include "elfzom1b.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "mpbird.mm"
include "iccpartimp.mm"
include "syl3anc.mm"
include "simprd.mm"
include "zcnd.mm"
include "npcan1.mm"
include "fveq2d.mm"
include "breqtrrd.mm"

theorem iccpartgtprec
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )
  assume iccpartgtprec.i: |- ( ph -> I e. ( 1 ... M ) )


  assert |- ( ph -> ( P ` ( I - 1 ) ) < ( P ` I ) )

  proof
    wph
    cI
    c1
    cmin
    co
    #
    cP
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cI
    cP
    cfv
    clt
    wph
    cP
    cxr
    cc0
    cM
    cfz
    co
    cmap
    co
    wcel
    #
    @1
    @3
    clt
    wbr
    #
    wph
    cM
    cn
    wcel
    cP
    cM
    ciccp
    cfv
    wcel
    @0
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @4
    @5
    wa
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @7
    cI
    c1
    cM
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    wph
    cI
    c1
    cM
    cfz
    co
    #
    wcel
    #
    @10
    iccpartgtprec.i
    wph
    cM
    cz
    wcel
    #
    @12
    @10
    wb
    wph
    cM
    iccpartgtprec.m
    nnzd
    #
    @13
    @11
    @9
    cI
    c1
    cM
    fzval3
    eleq2d
    syl
    mpbid
    wph
    @7
    @0
    cc0
    @8
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    @10
    wph
    @6
    @16
    @0
    wph
    cM
    @15
    cc0
    cfzo
    wph
    @15
    cM
    wph
    cM
    cc
    wcel
    @15
    cM
    wceq
    wph
    cM
    iccpartgtprec.m
    nncnd
    cM
    pncan1
    syl
    eqcomd
    oveq2d
    eleq2d
    wph
    cI
    cz
    wcel
    #
    @8
    cz
    wcel
    @10
    @17
    wb
    wph
    @12
    @18
    iccpartgtprec.i
    cI
    c1
    cM
    elfzelz
    syl
    #
    wph
    cM
    @14
    peano2zd
    cI
    @8
    elfzom1b
    syl2anc
    bitr4d
    mpbird
    cP
    @0
    cM
    iccpartimp
    syl3anc
    simprd
    wph
    cI
    @2
    cP
    wph
    @2
    cI
    wph
    cI
    cc
    wcel
    @2
    cI
    wceq
    wph
    cI
    @19
    zcnd
    cI
    npcan1
    syl
    eqcomd
    fveq2d
    breqtrrd
end
