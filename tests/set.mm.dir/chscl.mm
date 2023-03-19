include "cph.mm"
include "co.mm"
include "csh.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cch.mm"
include "chsh.mm"
include "syl.mm"
include "shscl.mm"
include "syl2anc.mm"
include "cfv.mm"
include "cpjh.mm"
include "cmpt.mm"
include "adantr.mm"
include "cort.mm"
include "wss.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "chscllem4.mm"
include "ex.mm"
include "alrimivv.mm"
include "isch2.mm"
include "sylanbrc.mm"

theorem chscl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vj: setvar j
  let vn: setvar n
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  assume chscl.1: |- ( ph -> A e. CH )
  assume chscl.2: |- ( ph -> B e. CH )
  assume chscl.3: |- ( ph -> B C_ ( _|_ ` A ) )


  assert |- ( ph -> ( A +H B ) e. CH )

  proof
    wph
    cA
    cB
    cph
    co
    #
    csh
    wcel
    #
    cn
    @0
    vf
    cv
    #
    wf
    #
    @2
    vz
    cv
    #
    chli
    wbr
    #
    wa
    #
    @4
    @0
    wcel
    #
    wi
    #
    vz
    wal
    vf
    wal
    @0
    cch
    wcel
    wph
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    @1
    wph
    cA
    cch
    wcel
    #
    @9
    chscl.1
    cA
    chsh
    syl
    wph
    cB
    cch
    wcel
    #
    @10
    chscl.2
    cB
    chsh
    syl
    cA
    cB
    shscl
    syl2anc
    wph
    @8
    vf
    vz
    wph
    @6
    @7
    wph
    @6
    wa
    vz
    cA
    cB
    vx
    vx
    cn
    vx
    cv
    @2
    cfv
    #
    cA
    cpjh
    cfv
    cfv
    cmpt
    #
    vx
    cn
    @13
    cB
    cpjh
    cfv
    cfv
    cmpt
    #
    @2
    wph
    @11
    @6
    chscl.1
    adantr
    wph
    @12
    @6
    chscl.2
    adantr
    wph
    cB
    cA
    cort
    cfv
    wss
    @6
    chscl.3
    adantr
    wph
    @3
    @5
    simprl
    wph
    @3
    @5
    simprr
    @14
    eqid
    @15
    eqid
    chscllem4
    ex
    alrimivv
    vz
    vf
    @0
    isch2
    sylanbrc
end
