include "covol.mm"
include "cfv.mm"
include "cioo.mm"
include "cv.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "cinf.mm"
include "eqid.mm"
include "ovolval.mm"
include "syl.mm"
include "csumge0.mm"
include "a1i.mm"
include "wcel.mm"
include "cz.mm"
include "cvv.mm"
include "reex.mm"
include "xpex.mm"
include "inss2.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "1zzd.mm"
include "adantl.mm"
include "nnuz.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "cc.mm"
include "absfico.mm"
include "subf.mm"
include "fco.mm"
include "rr2sscn2.mm"
include "elmapi.mm"
include "fcoss.mm"
include "sge0seq.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "rabbidv.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "infeq1d.mm"
include "eqtrd.mm"

theorem ovolval2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume ovolval2.a: |- ( ph -> A C_ RR )
  assume ovolval2.m: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = ( sum^ ` ( ( abs o. - ) o. f ) ) ) }

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint f ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    cA
    covol
    cfv
    #
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vy
    cv
    #
    caddc
    cabs
    cmin
    ccom
    #
    @1
    ccom
    #
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cM
    cxr
    clt
    cinf
    wph
    cA
    cr
    wss
    @0
    @15
    wceq
    ovolval2.a
    vy
    cA
    vf
    @14
    @14
    eqid
    #
    ovolval
    syl
    wph
    cxr
    @14
    cM
    clt
    wph
    @14
    @14
    @2
    @3
    @5
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @12
    wrex
    #
    vy
    cxr
    crab
    #
    cM
    @14
    @14
    wceq
    wph
    @16
    a1i
    wph
    @13
    @20
    vy
    cxr
    wph
    @9
    @19
    vf
    @12
    wph
    @1
    @12
    wcel
    #
    wa
    #
    @8
    @18
    @2
    @23
    @7
    @17
    @3
    @23
    @17
    @7
    @23
    @5
    @6
    c1
    cn
    @22
    c1
    cz
    wcel
    #
    wph
    @22
    @1
    @10
    cn
    cmap
    co
    #
    wcel
    #
    @24
    @12
    @25
    @1
    @10
    cvv
    wcel
    @11
    @10
    wss
    @12
    @25
    wss
    cr
    cr
    reex
    reex
    xpex
    cle
    @10
    inss2
    @11
    @10
    cn
    cvv
    mapss
    mp2an
    sseli
    #
    @26
    1zzd
    syl
    adantl
    nnuz
    @22
    cn
    cc0
    cpnf
    cico
    co
    #
    @5
    wf
    wph
    @22
    cc
    cc
    cxp
    #
    @28
    @10
    cn
    @4
    @1
    @29
    @28
    @4
    wf
    #
    @22
    cc
    @28
    cabs
    wf
    @29
    cc
    cmin
    wf
    @30
    absfico
    subf
    @29
    cc
    @28
    cabs
    cmin
    fco
    mp2an
    a1i
    @10
    @29
    wss
    @22
    rr2sscn2
    a1i
    @22
    @26
    cn
    @10
    @1
    wf
    @27
    @1
    @10
    cn
    elmapi
    syl
    fcoss
    adantl
    @6
    eqid
    sge0seq
    eqcomd
    eqeq2d
    anbi2d
    rexbidva
    rabbidv
    @21
    cM
    wceq
    wph
    cM
    @21
    ovolval2.m
    eqcomi
    a1i
    3eqtrd
    infeq1d
    eqtrd
end
