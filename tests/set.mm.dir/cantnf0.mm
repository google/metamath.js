include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "cv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "eqid.mm"
include "wcel.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "fconst6g.mm"
include "syl.mm"
include "con0.mm"
include "fczfsuppd.mm"
include "cantnfs.mm"
include "mpbir2and.mm"
include "cantnfval.mm"
include "wceq.mm"
include "eqidd.mm"
include "wfn.mm"
include "wb.mm"
include "0ex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "a1i.mm"
include "fnsuppeq0.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "oieq2.mm"
include "dmeqd.mm"
include "cen.mm"
include "wwe.mm"
include "we0.mm"
include "oien.mm"
include "mp2an.mm"
include "en0.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "seqom0g.mm"
include "3eqtrd.mm"

theorem cantnf0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cT: class T
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )
  assume cantnf0.a: |- ( ph -> (/) e. A )


  assert |- ( ph -> ( ( A CNF B ) ` ( B X. { (/) } ) ) = (/) )

  proof
    wph
    cB
    c0
    csn
    cxp
    #
    cA
    cB
    ccnf
    co
    cfv
    @0
    c0
    csupp
    co
    #
    cep
    coi
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    @2
    cfv
    #
    coe
    co
    @4
    @0
    cfv
    comu
    co
    vz
    cv
    coa
    co
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    c0
    @6
    cfv
    #
    c0
    wph
    vz
    cA
    cB
    cS
    vk
    @0
    @2
    @6
    cantnfs.s
    cantnfs.a
    cantnfs.b
    @2
    eqid
    wph
    @0
    cS
    wcel
    cB
    cA
    @0
    wf
    #
    @0
    c0
    cfsupp
    wbr
    wph
    c0
    cA
    wcel
    @8
    cantnf0.a
    cB
    c0
    cA
    fconst6g
    syl
    wph
    cB
    con0
    cA
    c0
    cantnfs.b
    cantnf0.a
    fczfsuppd
    wph
    cA
    cB
    cS
    @0
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    mpbir2and
    @6
    eqid
    #
    cantnfval
    wph
    @3
    c0
    @6
    wph
    @3
    c0
    cep
    coi
    #
    cdm
    #
    c0
    wph
    @2
    @10
    wph
    @1
    c0
    wceq
    #
    @2
    @10
    wceq
    wph
    @12
    @0
    @0
    wceq
    #
    wph
    @0
    eqidd
    wph
    @0
    cB
    wfn
    #
    cB
    con0
    wcel
    c0
    cvv
    wcel
    #
    @12
    @13
    wb
    @15
    @14
    wph
    0ex
    cB
    c0
    cvv
    fnconstg
    mp1i
    cantnfs.b
    @15
    wph
    0ex
    a1i
    cB
    @0
    cvv
    con0
    c0
    fnsuppeq0
    syl3anc
    mpbird
    @1
    c0
    cep
    oieq2
    syl
    dmeqd
    @11
    c0
    cen
    wbr
    #
    @11
    c0
    wceq
    @15
    c0
    cep
    wwe
    @16
    0ex
    cep
    we0
    c0
    cep
    @10
    cvv
    @10
    eqid
    oien
    mp2an
    @11
    en0
    mpbi
    syl6eq
    fveq2d
    @15
    @7
    c0
    wceq
    wph
    0ex
    @5
    @6
    c0
    cvv
    @9
    seqom0g
    mp1i
    3eqtrd
end
