include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "wo.mm"
include "cin.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "uztric.mm"
include "wss.mm"
include "uzss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eluzle.mm"
include "iftrue.mm"
include "syl.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "df-ss.mm"
include "wb.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "cr.mm"
include "zre.mm"
include "letri3.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "biimprcd.mm"
include "eqeq1d.mm"
include "sylibrd.mm"
include "com12.mm"
include "iffalse.mm"
include "pm2.61d1.mm"
include "jaoi.mm"

theorem uzin
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( ZZ>= ` M ) i^i ( ZZ>= ` N ) ) = ( ZZ>= ` if ( M <_ N , N , M ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cM
    cN
    cuz
    cfv
    #
    wcel
    #
    wo
    @2
    @4
    cin
    #
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cuz
    cfv
    #
    wceq
    #
    cM
    cN
    uztric
    @3
    @10
    @5
    @3
    @6
    @4
    @9
    @3
    @4
    @2
    wss
    @6
    @4
    wceq
    cM
    cN
    uzss
    @4
    @2
    sseqin2
    sylib
    @3
    @8
    cN
    cuz
    @3
    @7
    @8
    cN
    wceq
    cM
    cN
    eluzle
    @7
    cN
    cM
    iftrue
    #
    syl
    fveq2d
    eqtr4d
    @5
    @6
    @2
    @9
    @5
    @2
    @4
    wss
    @6
    @2
    wceq
    cN
    cM
    uzss
    @2
    @4
    df-ss
    sylib
    @5
    @8
    cM
    cuz
    @5
    @7
    @8
    cM
    wceq
    #
    @7
    @5
    @12
    @7
    @5
    cN
    cM
    wceq
    #
    @12
    @5
    @13
    @7
    @5
    @13
    cN
    cM
    cle
    wbr
    #
    @7
    wa
    #
    @7
    @5
    @1
    @0
    @13
    @15
    wb
    #
    cN
    cM
    eluzel2
    cN
    cM
    eluzelz
    @1
    cN
    cr
    wcel
    cM
    cr
    wcel
    @16
    @0
    cN
    zre
    cM
    zre
    cN
    cM
    letri3
    syl2an
    syl2anc
    @5
    @14
    @7
    cN
    cM
    eluzle
    biantrurd
    bitr4d
    biimprcd
    @7
    @8
    cN
    cM
    @11
    eqeq1d
    sylibrd
    com12
    @7
    cN
    cM
    iffalse
    pm2.61d1
    fveq2d
    eqtr4d
    jaoi
    syl
end
