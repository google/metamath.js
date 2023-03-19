include "cn.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cesum.mm"
include "cxad.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "cicc.mm"
include "wceq.mm"
include "wss.mm"
include "icossicc.mm"
include "fss.mm"
include "mpan2.mm"
include "esumfsup.mm"
include "syl.mm"
include "1zzd.mm"
include "cuz.mm"
include "wcel.mm"
include "elnnuz.mm"
include "ffvelrn.mm"
include "sylan2br.mm"
include "wa.mm"
include "ge0addcl.mm"
include "adantl.mm"
include "cr.mm"
include "rge0ssre.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprr.mm"
include "rexadd.mm"
include "eqcomd.mm"
include "syl2anc.mm"
include "seqfeq3.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eqtr4d.mm"

theorem esumfsupre
  let vk: setvar k
  let cF: class F
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume esumfsup.1: |- F/_ k F


  assert |- ( F : NN --> ( 0 [,) +oo ) -> sum* k e. NN ( F ` k ) = sup ( ran seq 1 ( + , F ) , RR* , < ) )

  proof
    cn
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    cn
    vk
    cv
    cF
    cfv
    vk
    cesum
    #
    cxad
    cF
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    caddc
    cF
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    @1
    cn
    cc0
    cpnf
    cicc
    co
    #
    cF
    wf
    #
    @2
    @5
    wceq
    @1
    @0
    @8
    wss
    @9
    cc0
    cpnf
    icossicc
    cn
    @0
    @8
    cF
    fss
    mpan2
    vk
    cF
    esumfsup.1
    esumfsup
    syl
    @1
    cxr
    @7
    @4
    clt
    @1
    @6
    @3
    @1
    vx
    vy
    caddc
    cxad
    @0
    cF
    c1
    @1
    1zzd
    vx
    cv
    #
    c1
    cuz
    cfv
    wcel
    @1
    @10
    cn
    wcel
    @10
    cF
    cfv
    @0
    wcel
    @10
    elnnuz
    cn
    @0
    @10
    cF
    ffvelrn
    sylan2br
    @10
    @0
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    wa
    #
    @10
    @12
    caddc
    co
    #
    @0
    wcel
    @1
    @10
    @12
    ge0addcl
    adantl
    @1
    @14
    wa
    #
    @10
    cr
    wcel
    #
    @12
    cr
    wcel
    #
    @15
    @10
    @12
    cxad
    co
    #
    wceq
    @16
    @0
    cr
    @10
    rge0ssre
    @1
    @11
    @13
    simprl
    sseldi
    @16
    @0
    cr
    @12
    rge0ssre
    @1
    @11
    @13
    simprr
    sseldi
    @17
    @18
    wa
    @19
    @15
    @10
    @12
    rexadd
    eqcomd
    syl2anc
    seqfeq3
    rneqd
    supeq1d
    eqtr4d
end
