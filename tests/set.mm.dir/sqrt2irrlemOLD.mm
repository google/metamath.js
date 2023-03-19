include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cexp.mm"
include "cmul.mm"
include "csqrt.mm"
include "cfv.mm"
include "cc.mm"
include "wceq.mm"
include "2cn.mm"
include "sqrtth.mm"
include "ax-mp.mm"
include "oveq1d.mm"
include "syl5eqr.mm"
include "zcnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "sqdivd.mm"
include "eqtrd.mm"
include "sqcld.mm"
include "nnsqcld.mm"
include "divcan1d.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "nnzd.mm"
include "wb.mm"
include "zesq.mm"
include "syl.mm"
include "mpbird.mm"
include "clt.mm"
include "wbr.mm"
include "sqvali.mm"
include "oveq2i.mm"
include "divdiv1d.mm"
include "3eqtr4a.mm"
include "zsqcl.mm"
include "eqeltrrd.mm"
include "nnrpd.mm"
include "rphalfcld.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnesq.mm"
include "jca.mm"

theorem sqrt2irrlemOLD
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume sqrt2irrlem.1: |- ( ph -> A e. ZZ )
  assume sqrt2irrlem.2: |- ( ph -> B e. NN )
  assume sqrt2irrlem.3: |- ( ph -> ( sqrt ` 2 ) = ( A / B ) )


  assert |- ( ph -> ( ( A / 2 ) e. ZZ /\ ( B / 2 ) e. NN ) )

  proof
    wph
    cA
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cB
    c2
    cdiv
    co
    cn
    wcel
    #
    wph
    @1
    cA
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wph
    @4
    wph
    @4
    cB
    c2
    cexp
    co
    #
    cn
    wph
    c2
    @6
    cmul
    co
    #
    c2
    cdiv
    co
    @4
    @6
    wph
    @7
    @3
    c2
    cdiv
    wph
    @7
    @3
    @6
    cdiv
    co
    #
    @6
    cmul
    co
    @3
    wph
    c2
    @8
    @6
    cmul
    wph
    c2
    cA
    cB
    cdiv
    co
    #
    c2
    cexp
    co
    #
    @8
    wph
    c2
    c2
    csqrt
    cfv
    #
    c2
    cexp
    co
    #
    @10
    c2
    cc
    wcel
    #
    @12
    c2
    wceq
    2cn
    c2
    sqrtth
    ax-mp
    wph
    @11
    @9
    c2
    cexp
    sqrt2irrlem.3
    oveq1d
    syl5eqr
    wph
    cA
    cB
    wph
    cA
    sqrt2irrlem.1
    zcnd
    #
    wph
    cB
    sqrt2irrlem.2
    nncnd
    wph
    cB
    sqrt2irrlem.2
    nnne0d
    sqdivd
    eqtrd
    oveq1d
    wph
    @3
    @6
    wph
    cA
    @14
    sqcld
    #
    wph
    @6
    wph
    cB
    sqrt2irrlem.2
    nnsqcld
    #
    nncnd
    #
    wph
    @6
    @16
    nnne0d
    divcan1d
    eqtrd
    oveq1d
    wph
    @6
    c2
    @17
    @13
    wph
    2cn
    a1i
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    divcan3d
    eqtr3d
    #
    @16
    eqeltrd
    nnzd
    wph
    cA
    cz
    wcel
    @1
    @5
    wb
    sqrt2irrlem.1
    cA
    zesq
    syl
    mpbird
    #
    wph
    @2
    @6
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wph
    @22
    cz
    wcel
    cc0
    @22
    clt
    wbr
    @23
    wph
    @0
    c2
    cexp
    co
    #
    @22
    cz
    wph
    @24
    @4
    c2
    cdiv
    co
    #
    @22
    wph
    @3
    c2
    c2
    cexp
    co
    #
    cdiv
    co
    @3
    c2
    c2
    cmul
    co
    #
    cdiv
    co
    @24
    @25
    @26
    @27
    @3
    cdiv
    c2
    2cn
    sqvali
    oveq2i
    wph
    cA
    c2
    @14
    @18
    @19
    sqdivd
    wph
    @3
    c2
    c2
    @15
    @18
    @18
    @19
    @19
    divdiv1d
    3eqtr4a
    wph
    @4
    @6
    c2
    cdiv
    @20
    oveq1d
    eqtrd
    wph
    @1
    @24
    cz
    wcel
    @21
    @0
    zsqcl
    syl
    eqeltrrd
    wph
    @22
    wph
    @6
    wph
    @6
    @16
    nnrpd
    rphalfcld
    rpgt0d
    @22
    elnnz
    sylanbrc
    wph
    cB
    cn
    wcel
    @2
    @23
    wb
    sqrt2irrlem.2
    cB
    nnesq
    syl
    mpbird
    jca
end
