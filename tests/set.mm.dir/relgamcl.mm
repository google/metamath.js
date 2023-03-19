include "crp.mm"
include "wcel.mm"
include "clgam.mm"
include "cfv.mm"
include "clog.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cr.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "rpdmgm.mm"
include "lgamcl.mm"
include "syl.mm"
include "relogcl.mm"
include "recnd.mm"
include "pncand.mm"
include "cv.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cseq.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqid.mm"
include "lgamcvg.mm"
include "wa.mm"
include "simpl.mm"
include "rpred.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "remulcld.mm"
include "1rp.mm"
include "a1i.mm"
include "rpaddcld.mm"
include "resubcld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "serfre.mm"
include "climrecl.mm"
include "eqeltrrd.mm"

theorem relgamcl
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( A e. RR+ -> ( log_G ` A ) e. RR )

  proof
    cA
    crp
    wcel
    #
    cA
    clgam
    cfv
    #
    cA
    clog
    cfv
    #
    caddc
    co
    #
    @2
    cmin
    co
    @1
    cr
    @0
    @1
    @2
    @0
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    @1
    cc
    wcel
    cA
    rpdmgm
    #
    cA
    lgamcl
    syl
    @0
    @2
    cA
    relogcl
    #
    recnd
    pncand
    @0
    @3
    @2
    @0
    @3
    vn
    caddc
    vm
    cn
    cA
    vm
    cv
    #
    c1
    caddc
    co
    #
    @6
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    @6
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    c1
    cseq
    #
    c1
    cn
    nnuz
    @0
    1zzd
    #
    @0
    cA
    vm
    @15
    @15
    eqid
    #
    @4
    lgamcvg
    @0
    cn
    cr
    vn
    cv
    #
    @16
    @0
    vn
    @15
    c1
    cn
    nnuz
    @17
    @0
    cn
    cr
    @19
    @15
    @0
    vm
    cn
    @14
    cr
    @15
    @0
    @6
    cn
    wcel
    #
    wa
    #
    @10
    @13
    @21
    cA
    @9
    @21
    cA
    @0
    @20
    simpl
    #
    rpred
    @21
    @8
    @21
    @7
    @6
    @21
    @7
    @21
    @6
    @0
    @20
    simpr
    #
    peano2nnd
    nnrpd
    @21
    @6
    @23
    nnrpd
    #
    rpdivcld
    relogcld
    remulcld
    @21
    @12
    @21
    @11
    c1
    @21
    cA
    @6
    @22
    @24
    rpdivcld
    c1
    crp
    wcel
    @21
    1rp
    a1i
    rpaddcld
    relogcld
    resubcld
    @18
    fmptd
    ffvelrnda
    serfre
    ffvelrnda
    climrecl
    @5
    resubcld
    eqeltrrd
end
