include "cop.mm"
include "csn.mm"
include "cstr.mm"
include "wbr.mm"
include "cn.mm"
include "wcel.mm"
include "cle.mm"
include "w3a.mm"
include "c0.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "nnrei.mm"
include "leidi.mm"
include "3pm3.2i.mm"
include "cvv.mm"
include "difss.mm"
include "eqeltri.mm"
include "funsng.mm"
include "mpan.mm"
include "funss.mm"
include "mpsyl.mm"
include "wn.mm"
include "fun0.mm"
include "opprc2.mm"
include "sneqd.mm"
include "difeq1d.mm"
include "difid.mm"
include "syl6eq.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "pm2.61i.mm"
include "dmsnopss.mm"
include "sneqi.mm"
include "cz.mm"
include "wceq.mm"
include "nnzi.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "sseqtri.mm"
include "isstruct.mm"
include "mpbir3an.mm"

theorem strle1
  let cA: class A
  let cI: class I
  let cX: class X
  assume strle1.i: |- I e. NN
  assume strle1.a: |- A = I


  assert |- { <. A , X >. } Struct <. I , I >.

  proof
    cA
    cX
    cop
    #
    csn
    #
    cI
    cI
    cop
    cstr
    wbr
    cI
    cn
    wcel
    #
    @2
    cI
    cI
    cle
    wbr
    #
    w3a
    @1
    c0
    csn
    #
    cdif
    #
    wfun
    #
    @1
    cdm
    #
    cI
    cI
    cfz
    co
    #
    wss
    @2
    @2
    @3
    strle1.i
    strle1.i
    cI
    cI
    strle1.i
    nnrei
    leidi
    3pm3.2i
    cX
    cvv
    wcel
    #
    @6
    @5
    @1
    wss
    @9
    @1
    wfun
    #
    @6
    @1
    @4
    difss
    cA
    cn
    wcel
    @9
    @10
    cA
    cI
    cn
    strle1.a
    strle1.i
    eqeltri
    cA
    cX
    cn
    cvv
    funsng
    mpan
    @5
    @1
    funss
    mpsyl
    @9
    wn
    #
    @6
    c0
    wfun
    fun0
    @11
    @5
    c0
    @11
    @5
    @4
    @4
    cdif
    c0
    @11
    @1
    @4
    @4
    @11
    @0
    c0
    cA
    cX
    opprc2
    sneqd
    difeq1d
    @4
    difid
    syl6eq
    funeqd
    mpbiri
    pm2.61i
    @7
    cA
    csn
    #
    @8
    cA
    cX
    dmsnopss
    @12
    cI
    csn
    #
    @8
    cA
    cI
    strle1.a
    sneqi
    cI
    cz
    wcel
    @8
    @13
    wceq
    cI
    strle1.i
    nnzi
    cI
    fzsn
    ax-mp
    eqtr4i
    sseqtri
    @1
    cI
    cI
    isstruct
    mpbir3an
end
