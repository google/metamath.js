include "cz.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "caddc.mm"
include "elz2.mm"
include "wa.mm"
include "reeanv.mm"
include "nnaddcl.mm"
include "adantr.mm"
include "adantl.mm"
include "cc.mm"
include "nncn.mm"
include "anim12i.mm"
include "addsub4.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "sylibr.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "rexlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem zaddcl
  let cM: class M
  let cN: class N
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M + N ) e. ZZ )

  proof
    cM
    cz
    wcel
    cM
    vx
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    wceq
    #
    vy
    cn
    wrex
    #
    vx
    cn
    wrex
    #
    cN
    vz
    cv
    #
    vw
    cv
    #
    cmin
    co
    #
    wceq
    #
    vw
    cn
    wrex
    #
    vz
    cn
    wrex
    #
    cM
    cN
    caddc
    co
    #
    cz
    wcel
    #
    cN
    cz
    wcel
    vx
    vy
    cM
    elz2
    vz
    vw
    cN
    elz2
    @5
    @11
    wa
    @4
    @10
    wa
    #
    vz
    cn
    wrex
    vx
    cn
    wrex
    @13
    @4
    @10
    vx
    vz
    cn
    cn
    reeanv
    @14
    @13
    vx
    vz
    cn
    cn
    @14
    @3
    @9
    wa
    #
    vw
    cn
    wrex
    vy
    cn
    wrex
    @0
    cn
    wcel
    #
    @6
    cn
    wcel
    #
    wa
    #
    @13
    @3
    @9
    vy
    vw
    cn
    cn
    reeanv
    @18
    @15
    @13
    vy
    vw
    cn
    cn
    @18
    @1
    cn
    wcel
    #
    @7
    cn
    wcel
    #
    wa
    #
    wa
    #
    @13
    @15
    @2
    @8
    caddc
    co
    #
    cz
    wcel
    #
    @22
    @23
    vu
    cv
    vv
    cv
    cmin
    co
    wceq
    vv
    cn
    wrex
    vu
    cn
    wrex
    #
    @24
    @22
    @0
    @6
    caddc
    co
    #
    cn
    wcel
    #
    @1
    @7
    caddc
    co
    #
    cn
    wcel
    #
    @23
    @26
    @28
    cmin
    co
    #
    wceq
    @25
    @18
    @27
    @21
    @0
    @6
    nnaddcl
    adantr
    @21
    @29
    @18
    @1
    @7
    nnaddcl
    adantl
    @22
    @30
    @23
    @18
    @0
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    wa
    @1
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    wa
    @30
    @23
    wceq
    @21
    @16
    @31
    @17
    @32
    @0
    nncn
    @6
    nncn
    anim12i
    @19
    @33
    @20
    @34
    @1
    nncn
    @7
    nncn
    anim12i
    @0
    @6
    @1
    @7
    addsub4
    syl2an
    eqcomd
    vu
    vv
    cn
    cn
    @26
    @28
    @23
    cmin
    rspceov
    syl3anc
    vu
    vv
    @23
    elz2
    sylibr
    @15
    @12
    @23
    cz
    cM
    @2
    cN
    @8
    caddc
    oveq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bir
    rexlimivv
    sylbir
    syl2anb
end
