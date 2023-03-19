include "cr.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cgam.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cc.mm"
include "eldifi.mm"
include "recnd.mm"
include "eldifn.mm"
include "eldifd.mm"
include "gamcl.mm"
include "syl.mm"
include "dmgmn0.mm"
include "divcan4d.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "ccxp.mm"
include "cmpt.mm"
include "cseq.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqid.mm"
include "gamcvg2.mm"
include "wa.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "rpge0d.mm"
include "adantr.mm"
include "recxpcld.mm"
include "nndivred.mm"
include "1red.mm"
include "readdcld.mm"
include "dmgmdivn0.mm"
include "redivcld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "remulcl.mm"
include "adantl.mm"
include "seqf.mm"
include "climrecl.mm"
include "eqeltrrd.mm"

theorem regamcl
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( A e. ( RR \ ( ZZ \ NN ) ) -> ( _G ` A ) e. RR )

  proof
    cA
    cr
    cz
    cn
    cdif
    #
    cdif
    wcel
    #
    cA
    cgam
    cfv
    #
    cA
    cmul
    co
    #
    cA
    cdiv
    co
    @2
    cr
    @1
    @2
    cA
    @1
    cA
    cc
    @0
    cdif
    wcel
    #
    @2
    cc
    wcel
    @1
    cA
    cc
    @0
    @1
    cA
    cA
    cr
    @0
    eldifi
    #
    recnd
    #
    cA
    cr
    @0
    eldifn
    eldifd
    #
    cA
    gamcl
    syl
    @6
    @1
    cA
    @7
    dmgmn0
    #
    divcan4d
    @1
    @3
    cA
    @1
    @3
    vn
    cmul
    vm
    cn
    vm
    cv
    #
    c1
    caddc
    co
    #
    @9
    cdiv
    co
    #
    cA
    ccxp
    co
    #
    cA
    @9
    cdiv
    co
    #
    c1
    caddc
    co
    #
    cdiv
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
    @1
    1zzd
    #
    @1
    cA
    vm
    @16
    @16
    eqid
    #
    @7
    gamcvg2
    @1
    cn
    cr
    vn
    cv
    #
    @17
    @1
    vn
    vx
    cmul
    cr
    @16
    c1
    cn
    nnuz
    @18
    @1
    cn
    cr
    @20
    @16
    @1
    vm
    cn
    @15
    cr
    @16
    @1
    @9
    cn
    wcel
    #
    wa
    #
    @12
    @14
    @22
    @11
    cA
    @22
    @11
    @22
    @10
    @9
    @22
    @10
    @22
    @9
    @1
    @21
    simpr
    #
    peano2nnd
    nnrpd
    @22
    @9
    @23
    nnrpd
    rpdivcld
    #
    rpred
    @22
    @11
    @24
    rpge0d
    @1
    cA
    cr
    wcel
    @21
    @5
    adantr
    #
    recxpcld
    @22
    @13
    c1
    @22
    cA
    @9
    @25
    @23
    nndivred
    @22
    1red
    readdcld
    @22
    cA
    @9
    @1
    @4
    @21
    @7
    adantr
    @23
    dmgmdivn0
    redivcld
    @19
    fmptd
    ffvelrnda
    @20
    cr
    wcel
    vx
    cv
    #
    cr
    wcel
    wa
    @20
    @26
    cmul
    co
    cr
    wcel
    @1
    @20
    @26
    remulcl
    adantl
    seqf
    ffvelrnda
    climrecl
    @5
    @8
    redivcld
    eqeltrrd
end
