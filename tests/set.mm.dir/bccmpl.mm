include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cbc.mm"
include "cmin.mm"
include "wceq.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "cdiv.mm"
include "bcval2.mm"
include "fznn0sub2.mm"
include "syl.mm"
include "cc.mm"
include "cn.mm"
include "elfznn0.mm"
include "faccl.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "elfz3nn0.mm"
include "elfzelz.mm"
include "nn0cn.mm"
include "zcn.mm"
include "nncan.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "adantl.mm"
include "wn.mm"
include "w3a.mm"
include "bcval3.mm"
include "simp1.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "sylan.mm"
include "3adant3.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "con3d.mm"
include "3impia.mm"
include "syl3anc.mm"
include "3expa.mm"
include "pm2.61dan.mm"

theorem bccmpl
  let cK: class K
  let cN: class N


  assert |- ( ( N e. NN0 /\ K e. ZZ ) -> ( N _C K ) = ( N _C ( N - K ) ) )

  proof
    cN
    cn0
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cK
    cbc
    co
    #
    cN
    cN
    cK
    cmin
    co
    #
    cbc
    co
    #
    wceq
    #
    @4
    @8
    @2
    @4
    @5
    cN
    cfa
    cfv
    #
    @6
    cfa
    cfv
    #
    cK
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @7
    cK
    cN
    bcval2
    @4
    @7
    @9
    cN
    @6
    cmin
    co
    #
    cfa
    cfv
    #
    @10
    cmul
    co
    #
    cdiv
    co
    #
    @13
    @4
    @6
    @3
    wcel
    #
    @7
    @17
    wceq
    cK
    cN
    fznn0sub2
    #
    @6
    cN
    bcval2
    syl
    @4
    @12
    @16
    @9
    cdiv
    @4
    @12
    @11
    @10
    cmul
    co
    @16
    @4
    @10
    @11
    @4
    @18
    @10
    cc
    wcel
    @19
    @18
    @10
    @18
    @6
    cn0
    wcel
    @10
    cn
    wcel
    @6
    cN
    elfznn0
    @6
    faccl
    syl
    nncnd
    syl
    @4
    @11
    @4
    cK
    cn0
    wcel
    @11
    cn
    wcel
    cK
    cN
    elfznn0
    cK
    faccl
    syl
    nncnd
    mulcomd
    @4
    @15
    @11
    @10
    cmul
    @4
    @14
    cK
    cfa
    @4
    @0
    @1
    @14
    cK
    wceq
    #
    cK
    cN
    elfz3nn0
    cK
    cc0
    cN
    elfzelz
    @0
    cN
    cc
    wcel
    cK
    cc
    wcel
    @20
    @1
    cN
    nn0cn
    cK
    zcn
    cN
    cK
    nncan
    syl2an
    #
    syl2anc
    fveq2d
    oveq1d
    eqtr4d
    oveq2d
    eqtr4d
    eqtr4d
    adantl
    @0
    @1
    @4
    wn
    #
    @8
    @0
    @1
    @22
    w3a
    #
    @5
    cc0
    @7
    cK
    cN
    bcval3
    @23
    @0
    @6
    cz
    wcel
    #
    @18
    wn
    #
    @7
    cc0
    wceq
    @0
    @1
    @22
    simp1
    @0
    @1
    @24
    @22
    @0
    cN
    cz
    wcel
    @1
    @24
    cN
    nn0z
    cN
    cK
    zsubcl
    sylan
    3adant3
    @0
    @1
    @22
    @25
    @2
    @18
    @4
    @18
    @14
    @3
    wcel
    @2
    @4
    @6
    cN
    fznn0sub2
    @2
    @14
    cK
    @3
    @21
    eleq1d
    syl5ib
    con3d
    3impia
    @6
    cN
    bcval3
    syl3anc
    eqtr4d
    3expa
    pm2.61dan
end
