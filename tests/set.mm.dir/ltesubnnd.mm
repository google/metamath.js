include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "zcnd.mm"
include "1cnd.mm"
include "nncnd.mm"
include "addsubd.mm"
include "clt.mm"
include "wbr.mm"
include "zred.mm"
include "nnrpd.mm"
include "ltsubrpd.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "nnzd.mm"
include "zsubcld.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"

theorem ltesubnnd
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume ltesubnnd.1: |- ( ph -> M e. ZZ )
  assume ltesubnnd.2: |- ( ph -> N e. NN )


  assert |- ( ph -> ( ( M + 1 ) - N ) <_ M )

  proof
    wph
    cM
    c1
    caddc
    co
    cN
    cmin
    co
    cM
    cN
    cmin
    co
    #
    c1
    caddc
    co
    #
    cM
    cle
    wph
    cM
    c1
    cN
    wph
    cM
    ltesubnnd.1
    zcnd
    wph
    1cnd
    wph
    cN
    ltesubnnd.2
    nncnd
    addsubd
    wph
    @0
    cM
    clt
    wbr
    #
    @1
    cM
    cle
    wbr
    #
    wph
    cM
    cN
    wph
    cM
    ltesubnnd.1
    zred
    wph
    cN
    ltesubnnd.2
    nnrpd
    ltsubrpd
    wph
    @0
    cz
    wcel
    cM
    cz
    wcel
    @2
    @3
    wb
    wph
    cM
    cN
    ltesubnnd.1
    wph
    cN
    ltesubnnd.2
    nnzd
    zsubcld
    ltesubnnd.1
    @0
    cM
    zltp1le
    syl2anc
    mpbid
    eqbrtrd
end
