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
include "covol.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cun.mm"
include "wcel.mm"
include "crp.mm"
include "simpld.mm"
include "simprd.mm"
include "rphalfcld.mm"
include "eqid.mm"
include "ovolgelb.mm"
include "syl3anc.mm"
include "reeanv.mm"
include "w3a.mm"
include "cif.mm"
include "cmpt.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "ovolunlem1.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem ovolunlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let vm: setvar m
  let cF: class F
  let vj: setvar j
  let cH: class H
  let cS: class S
  let cT: class T
  let cG: class G
  let cU: class U
  assume ovolun.a: |- ( ph -> ( A C_ RR /\ ( vol* ` A ) e. RR ) )
  assume ovolun.b: |- ( ph -> ( B C_ RR /\ ( vol* ` B ) e. RR ) )
  assume ovolun.c: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( vol* ` ( A u. B ) ) <_ ( ( ( vol* ` A ) + ( vol* ` B ) ) + C ) )

  proof
    wph
    cA
    cioo
    vg
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    caddc
    cabs
    cmin
    ccom
    #
    @0
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    cA
    covol
    cfv
    #
    cC
    c2
    cdiv
    co
    #
    caddc
    co
    cle
    wbr
    #
    wa
    #
    vg
    cle
    cr
    cr
    cxp
    cin
    cn
    cmap
    co
    #
    wrex
    #
    cB
    cioo
    vh
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    caddc
    @2
    @10
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    cB
    covol
    cfv
    #
    @5
    caddc
    co
    cle
    wbr
    #
    wa
    #
    vh
    @8
    wrex
    #
    cA
    cB
    cun
    covol
    cfv
    @4
    @13
    caddc
    co
    cC
    caddc
    co
    cle
    wbr
    #
    wph
    cA
    cr
    wss
    #
    @4
    cr
    wcel
    #
    @5
    crp
    wcel
    #
    @9
    wph
    @18
    @19
    ovolun.a
    simpld
    wph
    @18
    @19
    ovolun.a
    simprd
    wph
    cC
    ovolun.c
    rphalfcld
    #
    cA
    @5
    @3
    vg
    @3
    eqid
    #
    ovolgelb
    syl3anc
    wph
    cB
    cr
    wss
    #
    @13
    cr
    wcel
    #
    @20
    @16
    wph
    @23
    @24
    ovolun.b
    simpld
    wph
    @23
    @24
    ovolun.b
    simprd
    @21
    cB
    @5
    @12
    vh
    @12
    eqid
    #
    ovolgelb
    syl3anc
    @9
    @16
    wa
    @7
    @15
    wa
    #
    vh
    @8
    wrex
    vg
    @8
    wrex
    wph
    @17
    @7
    @15
    vg
    vh
    @8
    @8
    reeanv
    wph
    @26
    @17
    vg
    vh
    @8
    @8
    wph
    @0
    @8
    wcel
    #
    @10
    @8
    wcel
    #
    wa
    #
    @26
    @17
    wph
    @29
    @26
    w3a
    cA
    cB
    cC
    @3
    @12
    caddc
    @2
    vn
    cn
    vn
    cv
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    @31
    @10
    cfv
    @30
    c1
    caddc
    co
    c2
    cdiv
    co
    @0
    cfv
    cif
    cmpt
    #
    ccom
    c1
    cseq
    #
    vn
    @0
    @10
    @32
    wph
    @29
    @18
    @19
    wa
    @26
    ovolun.a
    3ad2ant1
    wph
    @29
    @23
    @24
    wa
    @26
    ovolun.b
    3ad2ant1
    wph
    @29
    cC
    crp
    wcel
    @26
    ovolun.c
    3ad2ant1
    @22
    @25
    @33
    eqid
    wph
    @27
    @28
    @26
    simp2l
    @1
    @6
    @15
    wph
    @29
    simp3ll
    @1
    @6
    @15
    wph
    @29
    simp3lr
    wph
    @27
    @28
    @26
    simp2r
    @11
    @14
    @7
    wph
    @29
    simp3rl
    @11
    @14
    @7
    wph
    @29
    simp3rr
    @32
    eqid
    ovolunlem1
    3exp
    rexlimdvv
    syl5bir
    mp2and
end
