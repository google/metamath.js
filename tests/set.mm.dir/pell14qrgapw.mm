include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "csqrt.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "eldifi.mm"
include "3ad2ant1.mm"
include "nnrpd.mm"
include "crp.mm"
include "1rp.mm"
include "rpaddcld.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "readdcld.mm"
include "pell14qrre.mm"
include "3adant3.mm"
include "df-2.mm"
include "1red.mm"
include "cexp.mm"
include "nnred.mm"
include "peano2re.mm"
include "syl.mm"
include "nnge1d.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "wceq.mm"
include "sq1.mm"
include "cc.mm"
include "nncnd.mm"
include "peano2cn.mm"
include "sqsqrtd.mm"
include "3brtr4d.mm"
include "cc0.mm"
include "cle.mm"
include "0le1.mm"
include "rpge0d.mm"
include "lt2sqd.mm"
include "mpbird.mm"
include "le2sqd.mm"
include "ltleaddd.mm"
include "syl5eqbr.mm"
include "pell14qrgap.mm"
include "ltletrd.mm"

theorem pell14qrgapw
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cB: class B
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ 1 < A ) -> 2 < A )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    w3a
    #
    c2
    cD
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    cD
    csqrt
    cfv
    #
    caddc
    co
    #
    cA
    c2
    cr
    wcel
    @3
    2re
    a1i
    @3
    @5
    @6
    @3
    @5
    @3
    @4
    @3
    cD
    c1
    @3
    cD
    @0
    @1
    cD
    cn
    wcel
    @2
    cD
    cn
    csquarenn
    eldifi
    3ad2ant1
    #
    nnrpd
    #
    c1
    crp
    wcel
    @3
    1rp
    a1i
    rpaddcld
    rpsqrtcld
    #
    rpred
    #
    @3
    @6
    @3
    cD
    @9
    rpsqrtcld
    #
    rpred
    #
    readdcld
    @0
    @1
    cA
    cr
    wcel
    @2
    cA
    cD
    pell14qrre
    3adant3
    @3
    c2
    c1
    c1
    caddc
    co
    @7
    clt
    df-2
    @3
    c1
    c1
    @5
    @6
    @3
    1red
    #
    @14
    @11
    @13
    @3
    c1
    @5
    clt
    wbr
    c1
    c2
    cexp
    co
    #
    @5
    c2
    cexp
    co
    #
    clt
    wbr
    @3
    c1
    @4
    @15
    @16
    clt
    @3
    c1
    cD
    @4
    @14
    @3
    cD
    @8
    nnred
    #
    @3
    cD
    cr
    wcel
    @4
    cr
    wcel
    @17
    cD
    peano2re
    syl
    @3
    cD
    @8
    nnge1d
    #
    @3
    cD
    @17
    ltp1d
    lelttrd
    @15
    c1
    wceq
    @3
    sq1
    a1i
    #
    @3
    @4
    @3
    cD
    cc
    wcel
    @4
    cc
    wcel
    @3
    cD
    @8
    nncnd
    #
    cD
    peano2cn
    syl
    sqsqrtd
    3brtr4d
    @3
    c1
    @5
    @14
    @11
    cc0
    c1
    cle
    wbr
    @3
    0le1
    a1i
    #
    @3
    @5
    @10
    rpge0d
    lt2sqd
    mpbird
    @3
    c1
    @6
    cle
    wbr
    @15
    @6
    c2
    cexp
    co
    #
    cle
    wbr
    @3
    c1
    cD
    @15
    @22
    cle
    @18
    @19
    @3
    cD
    @20
    sqsqrtd
    3brtr4d
    @3
    c1
    @6
    @14
    @13
    @21
    @3
    @6
    @12
    rpge0d
    le2sqd
    mpbird
    ltleaddd
    syl5eqbr
    cA
    cD
    pell14qrgap
    ltletrd
end
