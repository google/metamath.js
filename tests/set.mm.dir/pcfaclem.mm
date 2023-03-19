include "cn0.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cprime.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "nn0ge0.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "cn.mm"
include "prmnn.mm"
include "3ad2ant3.mm"
include "eluznn0.mm"
include "3adant3.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cmul.mm"
include "nn0red.mm"
include "eluzle.mm"
include "3ad2ant2.mm"
include "c2.mm"
include "prmuz2.mm"
include "bernneq3.mm"
include "syl2anc.mm"
include "lelttrd.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1red.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "cz.mm"
include "wa.mm"
include "nndivred.mm"
include "0z.mm"
include "flbi.mm"
include "sylancl.mm"
include "mpbir2and.mm"

theorem pcfaclem
  let cP: class P
  let cM: class M
  let cN: class N


  assert |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) /\ P e. Prime ) -> ( |_ ` ( N / ( P ^ M ) ) ) = 0 )

  proof
    cN
    cn0
    wcel
    #
    cM
    cN
    cuz
    cfv
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cN
    cP
    cM
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    cc0
    wceq
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @3
    cc0
    cN
    cle
    wbr
    #
    @7
    @0
    @1
    @10
    @2
    cN
    nn0ge0
    3ad2ant1
    @3
    cN
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @10
    @7
    wb
    @0
    @1
    @11
    @2
    cN
    nn0re
    3ad2ant1
    #
    @3
    @4
    @3
    cP
    cM
    @2
    @0
    cP
    cn
    wcel
    @1
    cP
    prmnn
    3ad2ant3
    @0
    @1
    cM
    cn0
    wcel
    #
    @2
    cM
    cN
    eluznn0
    3adant3
    #
    nnexpcld
    #
    nnred
    #
    @3
    @4
    @17
    nngt0d
    #
    cN
    @4
    ge0div
    syl3anc
    mpbid
    @3
    @5
    c1
    @8
    clt
    @3
    @5
    c1
    clt
    wbr
    #
    cN
    @4
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @3
    cN
    @4
    @21
    clt
    @3
    cN
    cM
    @4
    @14
    @3
    cM
    @16
    nn0red
    @18
    @1
    @0
    cN
    cM
    cle
    wbr
    @2
    cN
    cM
    eluzle
    3ad2ant2
    @3
    cP
    c2
    cuz
    cfv
    wcel
    #
    @15
    cM
    @4
    clt
    wbr
    @2
    @0
    @23
    @1
    cP
    prmuz2
    3ad2ant3
    @16
    cP
    cM
    bernneq3
    syl2anc
    lelttrd
    @3
    @4
    @3
    @4
    @17
    nncnd
    mulid1d
    breqtrrd
    @3
    @11
    c1
    cr
    wcel
    @12
    @13
    @20
    @22
    wb
    @14
    @3
    1red
    @18
    @19
    cN
    c1
    @4
    ltdivmul
    syl112anc
    mpbird
    0p1e1
    syl6breqr
    @3
    @5
    cr
    wcel
    cc0
    cz
    wcel
    @6
    @7
    @9
    wa
    wb
    @3
    cN
    @4
    @14
    @17
    nndivred
    0z
    @5
    cc0
    flbi
    sylancl
    mpbir2and
end
