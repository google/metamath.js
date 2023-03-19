include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "ccsh.mm"
include "co.mm"
include "oveq2.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "cwlks.mm"
include "crctiswlk.mm"
include "wlkf.mm"
include "3syl.mm"
include "cshw0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "syl5eq.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "cle.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "wb.mm"
include "crctcshlem1.mm"
include "nn0cnd.mm"
include "subid1d.mm"
include "breq2d.mm"
include "adantr.mm"
include "adantl.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "addid1d.mm"
include "sylan9eq.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "mpteq2dva.mm"
include "elfzle2.mm"
include "iftrued.mm"
include "chash.mm"
include "wf.mm"
include "wlkp.mm"
include "wfn.mm"
include "ffn.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "fneq2i.mm"
include "sylib.mm"
include "dffn5.mm"
include "eqcomd.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "jca.mm"

theorem crctcshlem4
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )
  assume crctcsh.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  assert |- ( ( ph /\ S = 0 ) -> ( H = F /\ Q = P ) )

  proof
    wph
    cS
    cc0
    wceq
    #
    wa
    #
    cH
    cF
    wceq
    cQ
    cP
    wceq
    @1
    cH
    cF
    cS
    ccsh
    co
    #
    cF
    crctcsh.h
    @0
    wph
    @2
    cF
    cc0
    ccsh
    co
    #
    cF
    cS
    cc0
    cF
    ccsh
    oveq2
    wph
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @3
    cF
    wceq
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @5
    crctcsh.d
    cP
    cF
    cG
    crctiswlk
    #
    cP
    cF
    cG
    cI
    crctcsh.i
    wlkf
    3syl
    @4
    cF
    cshw0
    syl
    sylan9eqr
    syl5eq
    @1
    cQ
    vx
    cc0
    cN
    cfz
    co
    #
    vx
    cv
    #
    cN
    cS
    cmin
    co
    #
    cle
    wbr
    #
    @10
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @13
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    #
    cP
    crctcsh.q
    @1
    @18
    vx
    @9
    @10
    cN
    cle
    wbr
    #
    @10
    cP
    cfv
    #
    @10
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cmpt
    #
    cP
    @1
    vx
    @9
    @17
    @23
    @1
    @10
    @9
    wcel
    #
    wa
    #
    @12
    @19
    @14
    @16
    @20
    @22
    @1
    @12
    @19
    wb
    @25
    @1
    @11
    cN
    @10
    cle
    @0
    wph
    @11
    cN
    cc0
    cmin
    co
    cN
    cS
    cc0
    cN
    cmin
    oveq2
    wph
    cN
    wph
    cN
    wph
    cP
    cF
    cG
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcshlem1
    nn0cnd
    subid1d
    sylan9eqr
    breq2d
    adantr
    @26
    @13
    @10
    cP
    @1
    @25
    @13
    @10
    cc0
    caddc
    co
    #
    @10
    @0
    @13
    @27
    wceq
    wph
    cS
    cc0
    @10
    caddc
    oveq2
    adantl
    @25
    @10
    @25
    @10
    @10
    cc0
    cN
    elfzelz
    zcnd
    addid1d
    sylan9eq
    #
    fveq2d
    @26
    @15
    @21
    cP
    @26
    @13
    @10
    cN
    cmin
    @28
    oveq1d
    fveq2d
    ifbieq12d
    mpteq2dva
    wph
    @24
    cP
    wceq
    @0
    wph
    @24
    vx
    @9
    @20
    cmpt
    #
    cP
    wph
    vx
    @9
    @23
    @20
    wph
    @25
    wa
    @19
    @20
    @22
    @25
    @19
    wph
    @10
    cc0
    cN
    elfzle2
    adantl
    iftrued
    mpteq2dva
    wph
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    @29
    cP
    wceq
    wph
    @6
    @7
    @32
    crctcsh.d
    @8
    cP
    cF
    cG
    cV
    crctcsh.v
    wlkp
    3syl
    wph
    @32
    wa
    #
    cP
    @29
    @33
    cP
    @9
    wfn
    #
    cP
    @29
    wceq
    @32
    @34
    wph
    @32
    cP
    @31
    wfn
    @34
    @31
    cV
    cP
    ffn
    @31
    @9
    cP
    @30
    cN
    cc0
    cfz
    cN
    @30
    crctcsh.n
    eqcomi
    oveq2i
    fneq2i
    sylib
    adantl
    vx
    @9
    cP
    dffn5
    sylib
    eqcomd
    mpdan
    eqtrd
    adantr
    eqtrd
    syl5eq
    jca
end
