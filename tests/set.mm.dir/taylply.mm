include "cc.mm"
include "ccnfld.mm"
include "crg.mm"
include "wcel.mm"
include "csubrg.mm"
include "cfv.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "subrgid.mm"
include "mp1i.mm"
include "cdvn.mm"
include "co.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "cpm.mm"
include "cn0.mm"
include "wss.mm"
include "cvv.mm"
include "wf.mm"
include "cnex.mm"
include "a1i.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "dvnbss.mm"
include "syl3anc.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "sseqtrd.mm"
include "recnprss.mm"
include "sstrd.mm"
include "sseldd.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "wa.mm"
include "cfa.mm"
include "adantr.mm"
include "elfznn0.mm"
include "adantl.mm"
include "dvnf.mm"
include "simpr.mm"
include "dvn2bss.mm"
include "ffvelrnd.mm"
include "cn.mm"
include "faccl.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "taylply2.mm"

theorem taylply
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cX: class X
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume taylpfval.t: |- T = ( N ( S Tayl F ) B )


  assert |- ( ph -> ( T e. ( Poly ` CC ) /\ ( deg ` T ) <_ N ) )

  proof
    wph
    cA
    cB
    cc
    cS
    cT
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylpfval.t
    ccnfld
    crg
    wcel
    cc
    ccnfld
    csubrg
    cfv
    wcel
    wph
    cnring
    cc
    ccnfld
    cnfldbas
    subrgid
    mp1i
    wph
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    cdm
    #
    cc
    cB
    wph
    @1
    cA
    cc
    wph
    @1
    cF
    cdm
    #
    cA
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    cN
    cn0
    wcel
    @1
    @2
    wss
    taylpfval.s
    wph
    cc
    cvv
    wcel
    #
    @4
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @5
    @6
    wph
    cnex
    a1i
    taylpfval.s
    taylpfval.f
    taylpfval.a
    cc
    cS
    cA
    cF
    cvv
    @3
    elpm2r
    syl22anc
    #
    taylpfval.n
    cS
    cF
    cN
    dvnbss
    syl3anc
    wph
    @7
    @2
    cA
    wceq
    taylpfval.f
    cA
    cc
    cF
    fdm
    syl
    sseqtrd
    wph
    cA
    cS
    cc
    taylpfval.a
    wph
    @4
    cS
    cc
    wss
    taylpfval.s
    cS
    recnprss
    syl
    sstrd
    sstrd
    taylpfval.b
    sseldd
    wph
    vk
    cv
    #
    cc0
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cB
    @9
    @0
    cfv
    #
    cfv
    @9
    cfa
    cfv
    #
    @11
    @12
    cdm
    #
    cc
    cB
    @12
    @11
    @4
    @5
    @9
    cn0
    wcel
    #
    @14
    cc
    @12
    wf
    wph
    @4
    @10
    taylpfval.s
    adantr
    #
    wph
    @5
    @10
    @8
    adantr
    #
    @10
    @15
    wph
    @9
    cN
    elfznn0
    adantl
    #
    cS
    cF
    @9
    dvnf
    syl3anc
    @11
    @1
    @14
    cB
    @11
    @4
    @5
    @10
    @1
    @14
    wss
    @16
    @17
    wph
    @10
    simpr
    cS
    cF
    @9
    cN
    dvn2bss
    syl3anc
    wph
    cB
    @1
    wcel
    @10
    taylpfval.b
    adantr
    sseldd
    ffvelrnd
    @11
    @13
    @11
    @15
    @13
    cn
    wcel
    @18
    @9
    faccl
    syl
    #
    nncnd
    @11
    @13
    @19
    nnne0d
    divcld
    taylply2
end
