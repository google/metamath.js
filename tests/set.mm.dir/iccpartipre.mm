include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "cxr.mm"
include "wcel.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cc0.mm"
include "cfz.mm"
include "cuz.mm"
include "wss.mm"
include "cn.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "nnz.mm"
include "peano2zm.mm"
include "id.mm"
include "zre.mm"
include "lem1d.mm"
include "3jca.mm"
include "syl.mm"
include "eluz2.mm"
include "sylibr.mm"
include "fzss2.mm"
include "cfzo.mm"
include "fzossfz.mm"
include "sseldi.mm"
include "wb.mm"
include "elfzoelz.mm"
include "nnzd.mm"
include "elfzm1b.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "sseldd.mm"
include "iccpartxr.mm"
include "1eluzge0.mm"
include "fzoss1.mm"
include "mp1i.mm"
include "syl6ss.mm"
include "fzofzp1.mm"
include "iccpartgtprec.mm"
include "cmap.mm"
include "ciccp.mm"
include "wa.mm"
include "iccpartimp.mm"
include "syl3anc.mm"
include "simprd.mm"
include "xrre2.mm"
include "syl32anc.mm"

theorem iccpartipre
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )
  assume iccpartipre.i: |- ( ph -> I e. ( 1 ..^ M ) )


  assert |- ( ph -> ( P ` I ) e. RR )

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
    cxr
    wcel
    cI
    cP
    cfv
    #
    cxr
    wcel
    cI
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cxr
    wcel
    @1
    @2
    clt
    wbr
    @2
    @4
    clt
    wbr
    #
    @2
    cr
    wcel
    wph
    cP
    @0
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    cc0
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    cM
    cfz
    co
    #
    @0
    wph
    cM
    @6
    cuz
    cfv
    wcel
    #
    @7
    @8
    wss
    wph
    cM
    cn
    wcel
    #
    @9
    iccpartgtprec.m
    @10
    @6
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @6
    cM
    cle
    wbr
    #
    w3a
    #
    @9
    @10
    @12
    @14
    cM
    nnz
    @12
    @11
    @12
    @13
    cM
    peano2zm
    @12
    id
    @12
    cM
    cM
    zre
    lem1d
    3jca
    syl
    @6
    cM
    eluz2
    sylibr
    syl
    @6
    cc0
    cM
    fzss2
    syl
    wph
    cI
    c1
    cM
    cfz
    co
    #
    wcel
    #
    @0
    @7
    wcel
    #
    wph
    c1
    cM
    cfzo
    co
    #
    @15
    cI
    c1
    cM
    fzossfz
    iccpartipre.i
    sseldi
    #
    wph
    cI
    cz
    wcel
    #
    @12
    @16
    @17
    wb
    wph
    cI
    @18
    wcel
    @20
    iccpartipre.i
    cI
    c1
    cM
    elfzoelz
    syl
    wph
    cM
    iccpartgtprec.m
    nnzd
    cI
    cM
    elfzm1b
    syl2anc
    mpbid
    sseldd
    iccpartxr
    wph
    cP
    cI
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @18
    @8
    cI
    wph
    @18
    cc0
    cM
    cfzo
    co
    #
    @8
    c1
    cc0
    cuz
    cfv
    wcel
    @18
    @21
    wss
    wph
    1eluzge0
    c1
    cc0
    cM
    fzoss1
    mp1i
    #
    cc0
    cM
    fzossfz
    syl6ss
    iccpartipre.i
    sseldd
    iccpartxr
    wph
    cP
    @3
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    cI
    @21
    wcel
    #
    @3
    @8
    wcel
    wph
    @18
    @21
    cI
    @22
    iccpartipre.i
    sseldd
    #
    cc0
    cM
    cI
    fzofzp1
    syl
    iccpartxr
    wph
    cP
    cI
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    @19
    iccpartgtprec
    wph
    cP
    cxr
    @8
    cmap
    co
    wcel
    #
    @5
    wph
    @10
    cP
    cM
    ciccp
    cfv
    wcel
    @23
    @25
    @5
    wa
    iccpartgtprec.m
    iccpartgtprec.p
    @24
    cP
    cI
    cM
    iccpartimp
    syl3anc
    simprd
    @1
    @2
    @4
    xrre2
    syl32anc
end
