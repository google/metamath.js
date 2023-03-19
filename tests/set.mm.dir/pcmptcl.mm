include "cn.mm"
include "wf.mm"
include "cmul.mm"
include "c1.mm"
include "cseq.mm"
include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "cif.mm"
include "wral.mm"
include "cn0.mm"
include "wi.mm"
include "pm2.27.mm"
include "wa.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantr.mm"
include "prmnn.mm"
include "nnexpcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "ex.mm"
include "syld.mm"
include "wn.mm"
include "iffalse.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "ralimi2.mm"
include "syl.mm"
include "fmpt.mm"
include "sylib.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ffvelrnda.mm"
include "nnmulcl.mm"
include "adantl.mm"
include "seqf.mm"
include "jca.mm"

theorem pcmptcl
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  let vp: setvar p
  let cB: class B
  let cM: class M
  let cN: class N
  let cP: class P
  assume pcmpt.1: |- F = ( n e. NN |-> if ( n e. Prime , ( n ^ A ) , 1 ) )
  assume pcmpt.2: |- ( ph -> A. n e. Prime A e. NN0 )


  assert |- ( ph -> ( F : NN --> NN /\ seq 1 ( x. , F ) : NN --> NN ) )

  proof
    wph
    cn
    cn
    cF
    wf
    #
    cn
    cn
    cmul
    cF
    c1
    cseq
    wf
    wph
    vn
    cv
    #
    cprime
    wcel
    #
    @1
    cA
    cexp
    co
    #
    c1
    cif
    #
    cn
    wcel
    #
    vn
    cn
    wral
    #
    @0
    wph
    cA
    cn0
    wcel
    #
    vn
    cprime
    wral
    @6
    pcmpt.2
    @7
    @5
    vn
    cprime
    cn
    @2
    @7
    wi
    #
    @5
    @1
    cn
    wcel
    #
    @2
    @8
    @5
    wi
    @2
    @8
    @7
    @5
    @2
    @7
    pm2.27
    @2
    @7
    @5
    @2
    @7
    wa
    @4
    @3
    cn
    @2
    @4
    @3
    wceq
    @7
    @2
    @3
    c1
    iftrue
    adantr
    @2
    @9
    @7
    @3
    cn
    wcel
    @1
    prmnn
    @1
    cA
    nnexpcl
    sylan
    eqeltrd
    ex
    syld
    @2
    wn
    #
    @5
    @8
    @10
    @4
    c1
    cn
    @2
    @3
    c1
    iffalse
    1nn
    syl6eqel
    a1d
    pm2.61i
    a1d
    ralimi2
    syl
    vn
    cn
    cn
    @4
    cF
    pcmpt.1
    fmpt
    sylib
    #
    wph
    vk
    vp
    cmul
    cn
    cF
    c1
    cn
    nnuz
    wph
    1zzd
    wph
    cn
    cn
    vk
    cv
    #
    cF
    @11
    ffvelrnda
    @12
    cn
    wcel
    vp
    cv
    #
    cn
    wcel
    wa
    @12
    @13
    cmul
    co
    cn
    wcel
    wph
    @12
    @13
    nnmulcl
    adantl
    seqf
    jca
end
