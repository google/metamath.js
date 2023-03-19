include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cphi.mm"
include "cfv.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "codz.mm"
include "cmo.mm"
include "eulerth.mm"
include "wb.mm"
include "simp1.mm"
include "cn0.mm"
include "simp2.mm"
include "phicld.mm"
include "nnnn0d.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "1zzd.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "odzdvds.mm"
include "mpdan.mm"

theorem odzphi
  let cA: class A
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cK: class K


  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( odZ ` N ) ` A ) || ( phi ` N ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    cN
    cA
    cN
    cphi
    cfv
    #
    cexp
    co
    #
    c1
    cmin
    co
    cdvds
    wbr
    #
    cA
    cN
    codz
    cfv
    cfv
    @4
    cdvds
    wbr
    #
    @3
    @5
    cN
    cmo
    co
    c1
    cN
    cmo
    co
    wceq
    #
    @6
    cA
    cN
    eulerth
    @3
    @0
    @5
    cz
    wcel
    #
    c1
    cz
    wcel
    @8
    @6
    wb
    @0
    @1
    @2
    simp1
    #
    @3
    @1
    @4
    cn0
    wcel
    #
    @9
    @0
    @1
    @2
    simp2
    @3
    @4
    @3
    cN
    @10
    phicld
    nnnn0d
    #
    cA
    @4
    zexpcl
    syl2anc
    @3
    1zzd
    @5
    c1
    cN
    moddvds
    syl3anc
    mpbid
    @3
    @11
    @6
    @7
    wb
    @12
    cA
    @4
    cN
    odzdvds
    mpdan
    mpbid
end
