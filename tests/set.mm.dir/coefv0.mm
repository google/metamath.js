include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "wceq.mm"
include "0cn.mm"
include "eqid.mm"
include "coeid2.mm"
include "mpan2.mm"
include "cuz.mm"
include "wss.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzss2.mm"
include "syl.mm"
include "wa.mm"
include "c1.mm"
include "elfz1eq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "0exp0e1.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "wf.mm"
include "coef3.mm"
include "0nn0.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "mulid1d.mm"
include "sylan9eqr.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "cdif.mm"
include "cn.mm"
include "eldifn.mm"
include "wn.mm"
include "wo.mm"
include "eldifi.mm"
include "elfznn0.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "id.mm"
include "cz.mm"
include "0z.mm"
include "elfz3.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "syl6.mm"
include "mt3d.mm"
include "adantl.mm"
include "0expd.mm"
include "oveq2d.mm"
include "syl2an.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumss.mm"
include "fsum1.mm"
include "sylancr.mm"
include "3eqtr2d.mm"

theorem coefv0
  let cA: class A
  let cS: class S
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cM: class M
  let cG: class G
  let cN: class N
  assume coefv0.1: |- A = ( coeff ` F )


  assert |- ( F e. ( Poly ` S ) -> ( F ` 0 ) = ( A ` 0 ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cc0
    cF
    cfv
    #
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    cc0
    @4
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc0
    cc0
    cfz
    co
    #
    @7
    vk
    csu
    #
    cc0
    cA
    cfv
    #
    @0
    cc0
    cc
    wcel
    @1
    @8
    wceq
    0cn
    cA
    cS
    vk
    cF
    @2
    cc0
    coefv0.1
    @2
    eqid
    coeid2
    mpan2
    @0
    @9
    @3
    @7
    vk
    @0
    @2
    cc0
    cuz
    cfv
    #
    wcel
    @9
    @3
    wss
    @0
    @2
    cn0
    @12
    cS
    cF
    dgrcl
    nn0uz
    syl6eleq
    cc0
    cc0
    @2
    fzss2
    syl
    @0
    @4
    @9
    wcel
    #
    wa
    @7
    @11
    cc
    @13
    @0
    @7
    @11
    c1
    cmul
    co
    #
    @11
    @13
    @4
    cc0
    wceq
    #
    @7
    @14
    wceq
    @4
    cc0
    elfz1eq
    @15
    @5
    @11
    @6
    c1
    cmul
    @4
    cc0
    cA
    fveq2
    @15
    @6
    cc0
    cc0
    cexp
    co
    c1
    @4
    cc0
    cc0
    cexp
    oveq2
    0exp0e1
    syl6eq
    oveq12d
    #
    syl
    @0
    @11
    @0
    cn0
    cc
    cA
    wf
    #
    cc0
    cn0
    wcel
    @11
    cc
    wcel
    #
    cA
    cS
    cF
    coefv0.1
    coef3
    #
    0nn0
    cn0
    cc
    cc0
    cA
    ffvelrn
    sylancl
    #
    mulid1d
    #
    sylan9eqr
    @0
    @18
    @13
    @20
    adantr
    eqeltrd
    @0
    @4
    @3
    @9
    cdif
    wcel
    #
    wa
    #
    @7
    @5
    cc0
    cmul
    co
    cc0
    @23
    @6
    cc0
    @5
    cmul
    @23
    @4
    @22
    @4
    cn
    wcel
    #
    @0
    @22
    @24
    @13
    @4
    @3
    @9
    eldifn
    @22
    @24
    wn
    @15
    @13
    @22
    @24
    @15
    @22
    @4
    cn0
    wcel
    #
    @24
    @15
    wo
    @22
    @4
    @3
    wcel
    @25
    @4
    @3
    @9
    eldifi
    @4
    @2
    elfznn0
    syl
    #
    @4
    elnn0
    sylib
    ord
    @15
    @4
    cc0
    @9
    @15
    id
    cc0
    cz
    wcel
    #
    cc0
    @9
    wcel
    0z
    cc0
    elfz3
    ax-mp
    syl6eqel
    syl6
    mt3d
    adantl
    0expd
    oveq2d
    @23
    @5
    @0
    @17
    @25
    @5
    cc
    wcel
    @22
    @19
    @26
    cn0
    cc
    @4
    cA
    ffvelrn
    syl2an
    mul01d
    eqtrd
    @0
    cc0
    @2
    fzfid
    fsumss
    @0
    @10
    @14
    @11
    @0
    @27
    @14
    cc
    wcel
    @10
    @14
    wceq
    0z
    @0
    @14
    @11
    cc
    @21
    @20
    eqeltrd
    @7
    @14
    vk
    cc0
    @16
    fsum1
    sylancr
    @21
    eqtrd
    3eqtr2d
end
