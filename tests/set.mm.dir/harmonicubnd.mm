include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "clog.mm"
include "caddc.mm"
include "fzfid.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "flge1nn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "peano2re.mm"
include "syl.mm"
include "simpl.mm"
include "cc0.mm"
include "0red.mm"
include "1re.mm"
include "a1i.mm"
include "clt.mm"
include "0lt1.mm"
include "simpr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "cmin.mm"
include "cem.mm"
include "cicc.mm"
include "harmonicbnd.mm"
include "emre.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "lesubadd2d.mm"
include "mpbid.mm"
include "flle.mm"
include "adantr.mm"
include "logled.mm"
include "leadd1dd.mm"
include "letrd.mm"

theorem harmonicubnd
  let cA: class A
  let vm: setvar m
  let cN: class N

  disjoint A m
  disjoint N m
  assert |- ( ( A e. RR /\ 1 <_ A ) -> sum_ m e. ( 1 ... ( |_ ` A ) ) ( 1 / m ) <_ ( ( log ` A ) + 1 ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    @3
    clog
    cfv
    #
    c1
    caddc
    co
    #
    cA
    clog
    cfv
    #
    c1
    caddc
    co
    #
    @2
    @4
    @6
    vm
    @2
    c1
    @3
    fzfid
    @2
    @5
    @4
    wcel
    #
    wa
    @5
    @12
    @5
    cn
    wcel
    @2
    @5
    @3
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    @2
    @8
    cr
    wcel
    @9
    cr
    wcel
    @2
    @3
    @2
    @3
    cA
    flge1nn
    #
    nnrpd
    #
    relogcld
    #
    @8
    peano2re
    syl
    @2
    @10
    cr
    wcel
    @11
    cr
    wcel
    @2
    cA
    @2
    cA
    @0
    @1
    simpl
    #
    @2
    cc0
    c1
    cA
    @2
    0red
    c1
    cr
    wcel
    @2
    1re
    a1i
    #
    @17
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @0
    @1
    simpr
    ltletrd
    elrpd
    #
    relogcld
    #
    @10
    peano2re
    syl
    @2
    @7
    @8
    cmin
    co
    #
    c1
    cle
    wbr
    #
    @7
    @9
    cle
    wbr
    @2
    @21
    cem
    c1
    cicc
    co
    wcel
    #
    @22
    @2
    @3
    cn
    wcel
    @23
    @14
    vm
    @3
    harmonicbnd
    syl
    @23
    @21
    cr
    wcel
    cem
    @21
    cle
    wbr
    @22
    cem
    c1
    @21
    emre
    1re
    elicc2i
    simp3bi
    syl
    @2
    @7
    @8
    c1
    @13
    @16
    @18
    lesubadd2d
    mpbid
    @2
    @8
    @10
    c1
    @16
    @20
    @18
    @2
    @3
    cA
    cle
    wbr
    #
    @8
    @10
    cle
    wbr
    @0
    @24
    @1
    cA
    flle
    adantr
    @2
    @3
    cA
    @15
    @19
    logled
    mpbid
    leadd1dd
    letrd
end
