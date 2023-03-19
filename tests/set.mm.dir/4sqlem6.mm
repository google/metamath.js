include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cc0.mm"
include "cmin.mm"
include "caddc.mm"
include "cmo.mm"
include "0red.mm"
include "zred.mm"
include "nnred.mm"
include "rehalfcld.mm"
include "readdcld.mm"
include "nnrpd.mm"
include "modcld.mm"
include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "modge0.mm"
include "syl2anc.mm"
include "lesub1dd.mm"
include "df-neg.mm"
include "3brtr4g.mm"
include "modlt.mm"
include "nncnd.mm"
include "2halvesd.mm"
include "breqtrrd.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "jca.mm"

theorem 4sqlem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  assume 4sqlem5.2: |- ( ph -> A e. ZZ )
  assume 4sqlem5.3: |- ( ph -> M e. NN )
  assume 4sqlem5.4: |- B = ( ( ( A + ( M / 2 ) ) mod M ) - ( M / 2 ) )


  assert |- ( ph -> ( -u ( M / 2 ) <_ B /\ B < ( M / 2 ) ) )

  proof
    wph
    cM
    c2
    cdiv
    co
    #
    cneg
    #
    cB
    cle
    wbr
    cB
    @0
    clt
    wbr
    wph
    cc0
    @0
    cmin
    co
    cA
    @0
    caddc
    co
    #
    cM
    cmo
    co
    #
    @0
    cmin
    co
    #
    @1
    cB
    cle
    wph
    cc0
    @3
    @0
    wph
    0red
    wph
    @2
    cM
    wph
    cA
    @0
    wph
    cA
    4sqlem5.2
    zred
    wph
    cM
    wph
    cM
    4sqlem5.3
    nnred
    rehalfcld
    #
    readdcld
    #
    wph
    cM
    4sqlem5.3
    nnrpd
    #
    modcld
    #
    @5
    wph
    @2
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    cc0
    @3
    cle
    wbr
    @6
    @7
    @2
    cM
    modge0
    syl2anc
    lesub1dd
    @0
    df-neg
    4sqlem5.4
    3brtr4g
    wph
    cB
    @4
    @0
    clt
    4sqlem5.4
    wph
    @4
    @0
    clt
    wbr
    @3
    @0
    @0
    caddc
    co
    #
    clt
    wbr
    wph
    @3
    cM
    @11
    clt
    wph
    @9
    @10
    @3
    cM
    clt
    wbr
    @6
    @7
    @2
    cM
    modlt
    syl2anc
    wph
    cM
    wph
    cM
    4sqlem5.3
    nncnd
    2halvesd
    breqtrrd
    wph
    @3
    @0
    @0
    @8
    @5
    @5
    ltsubaddd
    mpbird
    syl5eqbr
    jca
end
