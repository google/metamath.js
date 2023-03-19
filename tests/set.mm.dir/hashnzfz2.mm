include "cdvds.mm"
include "csn.mm"
include "cima.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "c1.mm"
include "cmin.mm"
include "cc0.mm"
include "cuz.mm"
include "cn.mm"
include "wcel.mm"
include "wss.mm"
include "2nn.mm"
include "uznnssnn.mm"
include "ax-mp.mm"
include "sseldi.mm"
include "cz.mm"
include "2z.mm"
include "a1i.mm"
include "nnuz.mm"
include "2m1e1.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "hashnzfz.mm"
include "oveq1i.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "clt.mm"
include "0red.mm"
include "nnrecred.mm"
include "nnred.mm"
include "nngt0d.mm"
include "recgt0d.mm"
include "ltled.mm"
include "eluzle.mm"
include "syl.mm"
include "wb.mm"
include "nnzd.mm"
include "zlem1lt.mm"
include "sylancr.mm"
include "mpbid.mm"
include "syl5eqbrr.mm"
include "nnrpd.mm"
include "recgt1d.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "cr.mm"
include "wa.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "nndivred.mm"
include "flcld.mm"
include "zcnd.mm"
include "subid1d.mm"
include "3eqtrd.mm"

theorem hashnzfz2
  let wph: wff ph
  let cK: class K
  let cN: class N
  assume hashnzfz2.n: |- ( ph -> N e. ( ZZ>= ` 2 ) )
  assume hashnzfz2.k: |- ( ph -> K e. NN )


  assert |- ( ph -> ( # ` ( ( || " { N } ) i^i ( 2 ... K ) ) ) = ( |_ ` ( K / N ) ) )

  proof
    wph
    cdvds
    cN
    csn
    cima
    c2
    cK
    cfz
    co
    cin
    chash
    cfv
    cK
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    @1
    cc0
    cmin
    co
    @1
    wph
    c2
    cK
    cN
    wph
    c2
    cuz
    cfv
    #
    cn
    cN
    c2
    cn
    wcel
    @5
    cn
    wss
    2nn
    c2
    uznnssnn
    ax-mp
    hashnzfz2.n
    sseldi
    #
    c2
    cz
    wcel
    #
    wph
    2z
    a1i
    wph
    cK
    cn
    @2
    cuz
    cfv
    #
    hashnzfz2.k
    cn
    c1
    cuz
    cfv
    @8
    nnuz
    @2
    c1
    cuz
    2m1e1
    fveq2i
    eqtr4i
    syl6eleq
    hashnzfz
    wph
    @4
    cc0
    @1
    cmin
    wph
    @4
    c1
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cc0
    @3
    @9
    cfl
    @2
    c1
    cN
    cdiv
    2m1e1
    oveq1i
    fveq2i
    wph
    @10
    cc0
    wceq
    #
    cc0
    @9
    cle
    wbr
    #
    @9
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wph
    cc0
    @9
    wph
    0red
    wph
    cN
    @6
    nnrecred
    #
    wph
    cN
    wph
    cN
    @6
    nnred
    wph
    cN
    @6
    nngt0d
    recgt0d
    ltled
    wph
    @9
    c1
    @13
    clt
    wph
    c1
    cN
    clt
    wbr
    @9
    c1
    clt
    wbr
    wph
    c1
    @2
    cN
    clt
    2m1e1
    wph
    c2
    cN
    cle
    wbr
    #
    @2
    cN
    clt
    wbr
    #
    wph
    cN
    @5
    wcel
    @16
    hashnzfz2.n
    c2
    cN
    eluzle
    syl
    wph
    @7
    cN
    cz
    wcel
    @16
    @17
    wb
    2z
    wph
    cN
    @6
    nnzd
    c2
    cN
    zlem1lt
    sylancr
    mpbid
    syl5eqbrr
    wph
    cN
    wph
    cN
    @6
    nnrpd
    recgt1d
    mpbid
    0p1e1
    syl6breqr
    wph
    @9
    cr
    wcel
    cc0
    cz
    wcel
    @11
    @12
    @14
    wa
    wb
    @15
    0z
    @9
    cc0
    flbi
    sylancl
    mpbir2and
    syl5eq
    oveq2d
    wph
    @1
    wph
    @1
    wph
    @0
    wph
    cK
    cN
    wph
    cK
    hashnzfz2.k
    nnred
    @6
    nndivred
    flcld
    zcnd
    subid1d
    3eqtrd
end
